; lean/emit.lisp — генератор .lean для проверки первообразных (шаг LEAN.L1, карточка L1).
; Утверждение точечное: HasDerivAt (fun x : ℝ => F) (f x) x при гипотезах; доказательство —
; структурный терм HasDerivAt по дереву F (комбинаторы .add/.mul/.neg/.div/.pow/.comp) и
; convert … using 1 с равенством производной. Голова вне таблицы §1.3 — ответ (unsupported причина).
; Гипотезы §1.4: условия ответа (conditions) + автоматические по дереву F и f.
(module lean
  (export lean-emit-antiderivative lean-certificate lean-status lean-hash
          lean-results-add lean-results-clear lean-results-count
          lean-supported-heads lean-toolchain lean-mathlib))

; Версии Lean и mathlib — как у spivak-lean; при смене — qedra-lean/lean-toolchain.
(define lean-toolchain "leanprover/lean4:v4.34.0-rc2")
(define lean-mathlib "v4.34.0-rc2")

; Головы, которые генератор умеет переводить (таблица §1.3).
(define (lean-supported-heads)
  '(+ * - / ^ sqrt exp log sin cos tan atan asin acos sinh cosh tanh))

; Голова-функция выражения? (символ в голове списка)
(define (lean-call? e) (and (pair? e) (symbol? (car e))))

; ----- нормализация: tan и tanh раскрываются в sin/cos и sinh/cosh (так проще терм HasDerivAt) -----

(define (lean-normalize e)
  (if (not (pair? e))
      e
      (let ((h (car e))
            (args (map lean-normalize (cdr e))))
        (cond ((and (equal? h 'tan) (= (length args) 1))
               (list '/ (list 'sin (car args)) (list 'cos (car args))))
              ((and (equal? h 'tanh) (= (length args) 1))
               (list '/ (list 'sinh (car args)) (list 'cosh (car args))))
              (else (cons h args))))))

; ----- поиск неподдерживаемой головы; #f — можно переводить -----

(define (lean-bad-head e)
  (cond ((number? e) (if (equal? (type-of e) 'float) 'float #f))
        ((symbol? e) (if (member? e '(inf %i unknown)) e #f))
        ((not (pair? e)) 'value)
        ((not (member? (car e) (lean-supported-heads))) (car e))
        ((equal? (car e) '^)
         (let ((n (if (>= (length e) 3) (caddr e) #f)))
           (cond ((and (number? n) (integer? n)) #f)
                 ((and (number? n) (rational-number? n)) #f)
                 (else 'symbolic-exponent))))
        (else (let loop ((xs (cdr e)))
                (if (null? xs) #f
                    (let ((b (lean-bad-head (car xs))))
                      (if b b (loop (cdr xs)))))))))

(define (lean-unsupported-reason b)
  (cond ((equal? b 'float) "вещественная константа (не рациональная)")
        ((equal? b 'symbolic-exponent) "символьный показатель степени")
        ((equal? b 'value) "невыражение в ответе")
        (else (string-append "голова " (symbol->string b)))))

; ----- перевод выражений в Lean (все составные — в скобках: приоритетов не боимся) -----

(define (lean-join xs sep)
  (if (null? xs)
      ""
      (if (null? (cdr xs))
          (car xs)
          (let loop ((acc (car xs)) (rest (cdr xs)))
            (if (null? rest)
                acc
                (loop (string-append acc sep (car rest)) (cdr rest)))))))

(define (lean-number-lit n)
  (cond ((integer? n) (string-append "(" (number->string n) " : ℝ)"))
        ((equal? (type-of n) 'rational)
         (let ((parts (string-split (number->string n) "/")))
           (if (= (length parts) 2)
               (string-append "((" (car parts) " : ℝ) / (" (cadr parts) " : ℝ))")
               (string-append "(" (number->string n) " : ℝ)"))))
        (else (string-append "(" (number->string n) " : ℝ)"))))

(define (lean-expr e)
  (cond ((number? e) (lean-number-lit e))
        ((symbol? e)
         (cond ((equal? e 'pi) "Real.pi")
               (else (symbol->string e))))
        ((pair? e)
         (let ((h (car e)) (args (map lean-expr (cdr e))))
           (cond ((equal? h '+) (string-append "(" (lean-join args " + ") ")"))
                 ((equal? h '*) (string-append "(" (lean-join args " * ") ")"))
                 ((equal? h '-) (if (= (length args) 1)
                                    (string-append "(-" (car args) ")")
                                    (string-append "(" (lean-join args " - ") ")")))
                 ((equal? h '/) (string-append "(" (lean-join args " / ") ")"))
                 ((equal? h '^)
                  ; (b^p)^n при целом n и рациональном p даёт b^(p*n) — снимает ((a^(1/2))^2)
                  (if (and (pair? (cadr e)) (equal? (car (cadr e)) '^)
                           (integer? (caddr e)) (number? (caddr (cadr e)))
                           (not (integer? (caddr (cadr e)))))
                      (lean-power (car args) (* (caddr (cadr e)) (caddr e)))
                      (lean-power (car args) (caddr e))))
                 ((equal? h 'sqrt) (lean-power (car args) 1/2))
                 ((equal? h 'exp) (string-append "Real.exp (" (car args) ")"))
                 ((equal? h 'log) (string-append "Real.log (" (car args) ")"))
                 ((equal? h 'sin) (string-append "Real.sin (" (car args) ")"))
                 ((equal? h 'cos) (string-append "Real.cos (" (car args) ")"))
                 ((equal? h 'tan) (string-append "Real.tan (" (car args) ")"))
                 ((equal? h 'atan) (string-append "Real.arctan (" (car args) ")"))
                 ((equal? h 'asin) (string-append "Real.arcsin (" (car args) ")"))
                 ((equal? h 'acos) (string-append "Real.arccos (" (car args) ")"))
                 ((equal? h 'sinh) (string-append "Real.sinh (" (car args) ")"))
                 ((equal? h 'cosh) (string-append "Real.cosh (" (car args) ")"))
                 ((equal? h 'tanh) (string-append "Real.tanh (" (car args) ")"))
                 (else (string-append "(" (symbol->string h) " " (lean-join args " ") ")")))))
        (else "0")))

; (^ a n): n ≥ 0 — x ^ n; n < 0 — a⁻¹ ^ |n|; дробный — rpow с вещественным показателем
(define (lean-power base n)
  (cond ((and (integer? n) (= n 0)) "(1 : ℝ)")
        ((and (integer? n) (= n 1)) base)
        ((and (integer? n) (> n 0))
         (string-append "(" base " ^ " (number->string n) ")"))
        ((and (integer? n) (< n 0))
         ; скобки вокруг base обязательны: «Real.cos (x)⁻¹» Lean читает как «cos (x⁻¹)»
         (let ((k (- n)))
           (if (= k 1)
               (string-append "((" base ")⁻¹)")
               (string-append "(((" base ")⁻¹) ^ " (number->string k) ")"))))
        (else (string-append "(" base " ^ " (lean-number-lit n) ")"))))

; ----- страж пустых теорем (L4): есть ли x, при котором все гипотезы выполнены -----
; Несовместные гипотезы делают «passed» бессмысленным, поэтому рядом с каждой теоремой
; печатается example : ∃ x, h1 ∧ … ∧ hn, свидетель — точка, найденная численно здесь.

; численное значение дерева при x = v; #f — посчитать нельзя
(define (lean-num-eval e x v)
  (cond ((number? e) e)
        ((equal? e x) v)
        ((not (pair? e)) #f)
        ((equal? (car e) '+)
         (let loop ((xs (cdr e)) (acc 0))
           (if (null? xs) acc
               (let ((a (lean-num-eval (car xs) x v)))
                 (if a (loop (cdr xs) (+ acc a)) #f)))))
        ((equal? (car e) '*)
         (let loop ((xs (cdr e)) (acc 1))
           (if (null? xs) acc
               (let ((a (lean-num-eval (car xs) x v)))
                 (if a (loop (cdr xs) (* acc a)) #f)))))
        ((equal? (car e) '-)
         (if (null? (cddr e))
             (let ((a (lean-num-eval (cadr e) x v))) (if a (- a) #f))
             (let ((a (lean-num-eval (cadr e) x v)) (b (lean-num-eval (caddr e) x v)))
               (if (and a b) (- a b) #f))))
        ((equal? (car e) '/)
         (let ((a (lean-num-eval (cadr e) x v)) (b (lean-num-eval (caddr e) x v)))
           (if (and a b (not (equal? b 0))) (/ a b) #f)))
        ((equal? (car e) '^)
         (let ((a (lean-num-eval (cadr e) x v)) (p (caddr e)))
           (cond ((or (not a) (not (number? p))) #f)
                 ((and (integer? p) (not (< p 0)))
                  (let loop ((k p) (acc 1))
                    (if (equal? k 0) acc (loop (- k 1) (* acc a)))))
                 ; дробная степень считается через exp/log — так получаем float, а не алгебраическое число
                 ((and (number? a) (> (* 1.0 a) 0)) (exp (* (* 1.0 p) (log (* 1.0 a)))))
                 (else #f))))
        ((equal? (car e) 'cos) (let ((a (lean-num-eval (cadr e) x v))) (if a (cos a) #f)))
        ((equal? (car e) 'sin) (let ((a (lean-num-eval (cadr e) x v))) (if a (sin a) #f)))
        ((equal? (car e) 'tan) (let ((a (lean-num-eval (cadr e) x v))) (if a (tan a) #f)))
        ((equal? (car e) 'exp) (let ((a (lean-num-eval (cadr e) x v))) (if a (exp a) #f)))
        ((equal? (car e) 'log) (let ((a (lean-num-eval (cadr e) x v))) (if (and a (> (* 1.0 a) 0)) (log a) #f)))
        ; sqrt и гиперболические — через exp/log и явные формулы, чтобы получить float
        ((equal? (car e) 'sqrt)
         (let ((a (lean-num-eval (cadr e) x v))) (if (and a (> (* 1.0 a) 0)) (exp (* 0.5 (log (* 1.0 a)))) #f)))
        ((equal? (car e) 'sinh)
         (let ((a (lean-num-eval (cadr e) x v))) (if a (/ (- (exp a) (exp (- a))) 2.0) #f)))
        ((equal? (car e) 'cosh)
         (let ((a (lean-num-eval (cadr e) x v))) (if a (/ (+ (exp a) (exp (- a))) 2.0) #f)))
        ((equal? (car e) 'tanh)
         (let ((a (lean-num-eval (cadr e) x v)))
           (if a (let ((e2 (exp (* 2.0 a)))) (/ (- e2 1.0) (+ e2 1.0))) #f)))
        (else #f)))

; гипотеза выполнена при x = v — с запасом от нуля, чтобы свидетель проходил norm_num
(define (lean-hyp-holds? key x v)
  (let ((op (car key)))
    (cond ((equal? op '>)                                   ; ключ (list '> 0 u) — это «0 < u» (§1.4)
           (let ((a (lean-num-eval (caddr key) x v)))
             (and a (> (* 1.0 a) 1e-6))))
          ((equal? op '!=)
           (let ((a (lean-num-eval (cadr key) x v)))
             (and a (> (abs (* 1.0 a)) 1e-6))))
          ((equal? op 'in)                                  ; -1 < u < 1
           (let ((a (lean-num-eval (cadr key) x v)))
             (and a (> (* 1.0 a) -0.999999) (< (* 1.0 a) 0.999999))))
          (else #f))))

(define lean-vacuity-candidates (list 0 1 2 -1 3 -2 4 -3 5))

(define (lean-hyps-hold? hyps x v)
  (cond ((null? hyps) #t)
        ((lean-hyp-holds? (car (car hyps)) x v) (lean-hyps-hold? (cdr hyps) x v))
        (else #f)))

(define (lean-vacuity-point hyps x)
  (let loop ((cs lean-vacuity-candidates))
    (cond ((null? cs) #f)
          ((lean-hyps-hold? hyps x (car cs)) (car cs))
          (else (loop (cdr cs))))))
; пример «гипотезы совместны»; точка не нашлась — пример заведомо ложный, статус будет vacuous?
(define (lean-vacuity-example id hyps x)
  (if (null? hyps)
      ""
      (let ((point (lean-vacuity-point hyps x)))
        (if (not point)
            (string-append
             "-- vacuous-check: " id " — точка не найдена\n"
             "example : (0 : ℝ) = 1 := by norm_num\n\n")
            (let ((body (let loop ((hs hyps) (acc ""))
                          (if (null? hs) acc
                              (loop (cdr hs) (string-append acc (if (equal? acc "") "" " ∧ ")
                                                            "(" (cadr (car hs)) ")")))))
                  (holes (let loop ((hs hyps) (acc ""))
                           (if (null? hs) acc
                               (loop (cdr hs) (string-append acc (if (equal? acc "") "" ", ") "?_"))))))
              (string-append
               "-- vacuous-check: " id " (x = " (number->string point) ")\n"
               "example : ∃ x : ℝ, " body " := by\n"
               "  refine ⟨" (number->string point) ", " holes "⟩ <;> first\n"
               "    | (norm_num; done)\n"
               "    | (positivity; done)\n"
               "    | (exact Real.log_pos (by norm_num); done)\n"
               "    | (exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num); done)\n"
               "    | (constructor <;> norm_num; done)\n\n"))))))

; ----- гипотезы §1.4 -----

(define (lean-pos-type u) (string-append "0 < " (lean-expr u)))
(define (lean-ne-type u) (string-append (lean-expr u) " ≠ 0"))
(define (lean-interval-type u)
  (string-append "-1 < " (lean-expr u) " ∧ " (lean-expr u) " < 1"))

(define (lean-hyp-present? key hyps)
  (cond ((null? hyps) #f)
        ((equal? (car (car hyps)) key) #t)
        (else (lean-hyp-present? key (cdr hyps)))))

; гипотеза — (ключ тип); ключ сравнивается equal?, порядок сохраняется
(define (lean-add-hyp key type hyps)
  (if (lean-hyp-present? key hyps) hyps (append hyps (list (list key type)))))

; имя гипотезы по ключу: h1, h2, …
(define (lean-hyp-name key hyps)
  (let loop ((i 1) (hs hyps))
    (cond ((null? hs) #f)
          ((equal? (car (car hs)) key) (string-append "h" (number->string i)))
          (else (loop (+ i 1) (cdr hs))))))

; доказательство u ≠ 0: прямая гипотеза или ne_of_gt из 0 < u
(define (lean-ne-proof u hyps)
  (let ((direct (lean-hyp-name (list '!= u 0) hyps)))
    (if direct direct
        (let ((pos (lean-hyp-name (list '> 0 u) hyps)))
          (if pos (string-append "(ne_of_gt " pos ")") "(by positivity)")))))

(define (lean-pos-proof u hyps)
  (let ((p (lean-hyp-name (list '> 0 u) hyps)))
    (if p p "(by positivity)")))

(define (lean-interval-proof u hyps)
  (let ((p (lean-hyp-name (list 'in u) hyps)))
    (if p p "(by constructor <;> linarith)")))

; arcsin/arccos в mathlib требуют по отдельности u ≠ -1 и u ≠ 1; берём из гипотезы-конъюнкции
(define (lean-interval-ne-proofs u hyps)
  (let ((p (lean-hyp-name (list 'in u) hyps)))
    (if p (string-append "(ne_of_gt " p ".1) (ne_of_lt " p ".2)")
        "(by constructor <;> linarith) (by constructor <;> linarith)")))

; знаменатель-произведение даёт u ≠ 0 по каждому множителю: этого требует field_simp
; (из «x · (x²−1)^(1/2) ≠ 0» иначе не вывести «x ≠ 0»)
(define (lean-add-ne-hyps u hyps)
  (if (and (pair? u) (equal? (car u) '*))
      (let loop ((xs (cdr u)) (hs hyps))
        (if (null? xs) hs
            (loop (cdr xs) (lean-add-ne-hyps (car xs) hs))))
      (lean-add-hyp (list '!= u 0) (lean-ne-type u) hyps)))

; автоматические гипотезы по дереву: знаменатель, log/sqrt/rpow, asin/acos
(define (lean-collect-hyps e x hyps)
  (cond ((or (not (pair? e)) (null? e)) hyps)
        ((equal? (car e) '/)
         (let ((num (cadr e)) (den (caddr e)))
           (lean-collect-hyps num x
             (lean-collect-hyps den x
               (lean-add-ne-hyps den hyps)))))
        ((equal? (car e) '^)
         (let ((b (cadr e)) (n (caddr e)))
           (let ((h1 (lean-collect-hyps b x hyps)))
             (cond ((and (integer? n) (< n 0))
                    (lean-add-hyp (list '!= b 0) (lean-ne-type b) h1))
                   ((and (number? n) (rational-number? n) (not (integer? n)))
                    (lean-add-hyp (list '> 0 b) (lean-pos-type b) h1))
                   (else h1)))))
        ((equal? (car e) 'sqrt)
         (lean-collect-hyps (cadr e) x
           (lean-add-hyp (list '> 0 (cadr e)) (lean-pos-type (cadr e)) hyps)))
        ((equal? (car e) 'log)
         (lean-collect-hyps (cadr e) x
           (lean-add-hyp (list '> 0 (cadr e)) (lean-pos-type (cadr e)) hyps)))
        ((member? (car e) '(asin acos))
         (lean-collect-hyps (cadr e) x
           (lean-add-hyp (list 'in (cadr e)) (lean-interval-type (cadr e)) hyps)))
        (else (let loop ((xs (cdr e)) (hs hyps))
                (if (null? xs) hs
                    (loop (cdr xs) (lean-collect-hyps (car xs) x hs)))))))

; ----- условия ответа (conditions) → ключ+тип -----

; (conditions) отдаёт пары (условие "причина"); принимаем и голое условие
(define (lean-cond-core c)
  (if (and (pair? c) (= (length c) 2) (equal? (type-of (cadr c)) 'string))
      (car c)
      c))

; ключ нормируется так, чтобы (плюс u 0) и (больше 0 u) давали один ключ (упрощение сравнений с нулём)
(define (lean-zero? e) (and (number? e) (equal? e 0)))

(define (lean-cmp-key op a b)
  (cond ((and (member? op '(> >=)) (lean-zero? b)) (list op 0 a))
        ((and (member? op '(< <=)) (lean-zero? a))
         (list (if (equal? op '<) '> '>=) 0 b))
        (else (list op a b))))

(define (lean-cmp-type op a b)
  (cond ((and (member? op '(> >=)) (lean-zero? b))
         (string-append "0 " (if (equal? op '>) "< " "≤ ") (lean-expr a)))
        ((and (member? op '(< <=)) (lean-zero? a))
         (string-append "0 " (if (equal? op '<) "< " "≤ ") (lean-expr b)))
        (else (string-append (lean-expr a) " "
                             (cond ((equal? op '>) ">") ((equal? op '>=) "≥")
                                   ((equal? op '<) "<") (else "≤"))
                             " " (lean-expr b)))))

(define (lean-cond-entry c)
  (cond ((not (pair? c)) #f)
        ((member? (car c) '(> >= < <=))
         (let ((k (lean-cmp-key (car c) (cadr c) (caddr c))))
           (list k (lean-cmp-type (car c) (cadr c) (caddr c)))))
        ((member? (car c) '(= != /=))
         (let ((op (if (equal? (car c) '=) '= '!=)))
           (list (list op (cadr c) (caddr c))
                 (string-append (lean-expr (cadr c)) (if (equal? op '=) " = " " ≠ ") (lean-expr (caddr c))))))
        ((and (equal? (car c) 'not) (pair? (cadr c)) (equal? (car (cadr c)) '=))
         (list (list '!= (cadr (cadr c)) (caddr (cadr c)))
               (string-append (lean-expr (cadr (cadr c))) " ≠ " (lean-expr (caddr (cadr c))))))
        ((equal? (car c) 'positive) (list (list '> 0 (cadr c)) (lean-pos-type (cadr c))))
        ((equal? (car c) 'negative) (list (list '< 0 (cadr c)) (lean-neg-type (cadr c))))
        ((and (equal? (car c) 'and) (>= (length c) 2))
         (let ((entries (map lean-cond-entry (cdr c))))
           (if (any? (lambda (e) (not e)) entries)
               #f
               (list (cons 'and (map car entries))
                     (lean-join (map cadr entries) " ∧ ")))))
        ((and (equal? (car c) 'or) (>= (length c) 2))
         (let ((entries (map lean-cond-entry (cdr c))))
           (if (any? (lambda (e) (not e)) entries)
               #f
               (list (cons 'or (map car entries))
                     (lean-join (map cadr entries) " ∨ ")))))
        (else #f)))

(define (lean-neg-type u) (string-append (lean-expr u) " < 0"))

; разбор списка условий; (ok гипотезы) либо (unsupported причина)
(define (lean-conditions-entries cs hyps)
  (cond ((null? cs) (list 'ok hyps))
        (else
         (let ((c (lean-cond-core (car cs))))
           (if (null? c)
               (lean-conditions-entries (cdr cs) hyps)
               (let ((entry (lean-cond-entry c)))
                 (if entry
                     (lean-conditions-entries (cdr cs) (lean-add-hyp (car entry) (cadr entry) hyps))
                     (list 'unsupported (string-append "условие не переводится: " (to-string c))))))))))

(define (lean-list-of-conditions conditions)
  (cond ((null? conditions) '())
        ((pair? conditions) conditions)
        (else (list conditions))))

; ----- свободные параметры теоремы -----

(define (lean-add-var s vars)
  (if (or (equal? s 'x) (equal? s 'pi) (member? s vars)) vars (append vars (list s))))

(define (lean-collect-vars e vars)
  (cond ((symbol? e) (lean-add-var e vars))
        ((pair? e)
         (let loop ((xs (cdr e)) (vs vars))
           (if (null? xs) vs (loop (cdr xs) (lean-collect-vars (car xs) vs)))))
        (else vars)))

; ----- структурный терм HasDerivAt по дереву F -----

(define (lean-deriv-sum args x hyps)
  (cond ((null? args) "(hasDerivAt_const (x := x) (c := 0))")
        ((null? (cdr args)) (lean-deriv-term (car args) x hyps))
        (else (let loop ((acc (lean-deriv-term (car args) x hyps)) (rest (cdr args)))
                (if (null? rest) acc
                    (loop (string-append "(" acc ").add (" (lean-deriv-term (car rest) x hyps) ")")
                          (cdr rest)))))))

(define (lean-deriv-prod args x hyps)
  (cond ((null? args) "(hasDerivAt_const (x := x) (c := 1))")
        ((null? (cdr args)) (lean-deriv-term (car args) x hyps))
        (else (let loop ((acc (lean-deriv-term (car args) x hyps)) (rest (cdr args)))
                (if (null? rest) acc
                    (loop (string-append "(" acc ").mul (" (lean-deriv-term (car rest) x hyps) ")")
                          (cdr rest)))))))

; композиция нужна только когда аргумент — не сам x: иначе в терме остаётся f ∘ id
(define (lean-unary arg x hyps proof)
  (if (equal? arg 'x)
      proof
      (string-append "(" proof ").comp x (" (lean-deriv-term arg x hyps) ")")))

(define (lean-deriv-term e x hyps)
  (cond
    ((not (contains-sym? e x)) (string-append "(hasDerivAt_const (x := x) (c := " (lean-expr e) "))"))
    ((equal? e x) "(hasDerivAt_id x)")
    ((equal? (car e) '+) (lean-deriv-sum (cdr e) x hyps))
    ((equal? (car e) '*) (lean-deriv-prod (cdr e) x hyps))
    ((equal? (car e) '-)
     (if (= (length (cdr e)) 1)
         (string-append "(" (lean-deriv-term (cadr e) x hyps) ").neg")
         (string-append "((" (lean-deriv-term (cadr e) x hyps) ").sub ("
                        (lean-deriv-term (caddr e) x hyps) "))")))
    ((equal? (car e) '/)
     (string-append "((" (lean-deriv-term (cadr e) x hyps) ").div ("
                    (lean-deriv-term (caddr e) x hyps) ") "
                    (lean-ne-proof (caddr e) hyps) ")"))
    ((equal? (car e) '^)
     (let ((b (cadr e)) (n (caddr e)))
       (cond ((and (integer? n) (= n 0)) "(hasDerivAt_const (x := x) (c := 1))")
             ((and (integer? n) (= n 1)) (lean-deriv-term b x hyps))
             ((and (integer? n) (> n 0))
              (string-append "((" (lean-deriv-term b x hyps) ").pow " (number->string n) ")"))
             ((and (integer? n) (= n -1))
              (string-append "((" (lean-deriv-term b x hyps) ").inv " (lean-ne-proof b hyps) ")"))
             ((and (integer? n) (< n 0))
              (string-append "(((" (lean-deriv-term b x hyps) ").inv "
                             (lean-ne-proof b hyps) ").pow " (number->string (- n)) ")"))
             (else
              (lean-unary b x hyps
                          (string-append "(Real.hasDerivAt_rpow_const (x := " (lean-expr b)
                                         ") (p := " (lean-number-lit n) ") (Or.inl "
                                         (lean-ne-proof b hyps) "))"))))))
    ((equal? (car e) 'sqrt)
     (lean-unary (cadr e) x hyps
                 (string-append "(Real.hasDerivAt_sqrt " (lean-ne-proof (cadr e) hyps) ")")))
    ((equal? (car e) 'exp)
     (lean-unary (cadr e) x hyps
                 (string-append "(Real.hasDerivAt_exp (" (lean-expr (cadr e)) "))")))
    ((equal? (car e) 'log)
     (lean-unary (cadr e) x hyps
                 (string-append "(Real.hasDerivAt_log " (lean-ne-proof (cadr e) hyps) ")")))
    ((equal? (car e) 'sin)
     (lean-unary (cadr e) x hyps
                 (string-append "(Real.hasDerivAt_sin (" (lean-expr (cadr e)) "))")))
    ((equal? (car e) 'cos)
     (lean-unary (cadr e) x hyps
                 (string-append "(Real.hasDerivAt_cos (" (lean-expr (cadr e)) "))")))
    ((equal? (car e) 'atan)
     (lean-unary (cadr e) x hyps
                 (string-append "(Real.hasDerivAt_arctan (" (lean-expr (cadr e)) "))")))
    ((equal? (car e) 'asin)
     (lean-unary (cadr e) x hyps
                 (string-append "(Real.hasDerivAt_arcsin "
                                (lean-interval-ne-proofs (cadr e) hyps) ")")))
    ((equal? (car e) 'acos)
     (lean-unary (cadr e) x hyps
                 (string-append "(Real.hasDerivAt_arccos "
                                (lean-interval-ne-proofs (cadr e) hyps) ")")))
    ((equal? (car e) 'sinh)
     (lean-unary (cadr e) x hyps
                 (string-append "(Real.hasDerivAt_sinh (" (lean-expr (cadr e)) "))")))
    ((equal? (car e) 'cosh)
     (lean-unary (cadr e) x hyps
                 (string-append "(Real.hasDerivAt_cosh (" (lean-expr (cadr e)) "))")))
    (else "(hasDerivAt_const (x := x) (c := 0))")))

; ----- сборка текста теоремы -----

(define (lean-named-hyps hyps)
  (let loop ((i 1) (hs hyps) (acc '()))
    (if (null? hs)
        (reverse acc)
        (loop (+ i 1) (cdr hs)
              (cons (string-append "(h" (number->string i) " : " (cadr (car hs)) ")") acc)))))

; имена гипотез через запятую — для field_simp [h1, h2, …]
(define (lean-hyp-names hyps)
  (let loop ((i 1) (hs hyps) (acc '()))
    (if (null? hs)
        (lean-join (reverse acc) ", ")
        (loop (+ i 1) (cdr hs) (cons (string-append "h" (number->string i)) acc)))))

(define (lean-param-list vars hyps)
  (lean-join (append (list "(x : ℝ)")
                     (map (lambda (s) (string-append "(" (symbol->string s) " : ℝ)")) vars)
                     (lean-named-hyps hyps))
             " "))

(define (lean-conditions-comment conds)
  (if (null? conds)
      "[]"
      (string-append "[" (lean-join (map (lambda (c) (math-print c)) conds) ", ") "]")))

; вспомогательные леммы для rpow со степенью 1/2 — их порождает производная sqrt/степени
(define lean-helper-lemmas
  (string-append
   "-- qedra: леммы о rpow со степенью 1/2 (одинаковы во всех сертификатах)\n"
   "macro \"qedra_discharge\" : tactic =>\n"
   "  `(tactic| first | positivity | assumption | (apply ne_of_gt; assumption) | linarith)\n"
   "\n"
   "private lemma qedra_rpow_half_mul (a : ℝ) (ha : 0 < a) : a ^ (1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ) = 1 := by\n"
   "  rw [← Real.rpow_add ha]\n"
   "  norm_num\n"
   "\n"
   "private lemma qedra_rpow_half_sq (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by\n"
   "  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]\n"
   "  norm_num\n"
   "\n"
   "private lemma qedra_rpow_half_cube (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 2 : ℝ)) ^ 3 = a * a ^ (1 / 2 : ℝ) := by\n"
   "  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, qedra_rpow_half_sq a ha]\n"
   "\n"
   "private lemma qedra_rpow_half_neg (a : ℝ) (ha : 0 < a) : a ^ (-1 / 2 : ℝ) = a ^ (1 / 2 : ℝ) / a := by\n"
   "  rw [eq_div_iff (ne_of_gt ha)]\n"
   "  calc a ^ (-1 / 2 : ℝ) * a = a ^ (-1 / 2 : ℝ) * a ^ (1 : ℝ) := by rw [Real.rpow_one]\n"
   "    _ = a ^ (-1 / 2 + 1 : ℝ) := by rw [Real.rpow_add ha]\n"
   "    _ = a ^ (1 / 2 : ℝ) := by norm_num\n"
   "\n"
   "-- одна и та же обратная степень приходит двумя формами: (a^(1/2))⁻¹ и a^(−1/2)\n"
   "private lemma qedra_rpow_neg_half_inv (a : ℝ) (ha : 0 < a) : a ^ (-1 / 2 : ℝ) = (a ^ (1 / 2 : ℝ))⁻¹ := by\n"
   "  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (le_of_lt ha)]\n"
   "\n"))

(define (lean-theorem-text id f F fn Fn x conditions vars hyps)
  (let ((params (lean-param-list vars hyps))
        (hnames (lean-hyp-names hyps))
        (term (lean-deriv-term Fn x hyps)))
    (string-append
     "import Mathlib\n"
     "open Real\n"
     "\n"
     lean-helper-lemmas
     "-- qedra: integrate(" (math-print f) ", " (symbol->string x) ") -> " (math-print F)
     "; conditions: " (lean-conditions-comment conditions) "\n"
     "theorem qedra_int_" id (if (equal? params "") "" (string-append " " params)) " :\n"
     "    HasDerivAt (fun x : ℝ => " (lean-expr Fn) ") (" (lean-expr fn) ") x := by\n"
     "  have h := " term "\n"
     "  change HasDerivAt (fun x : ℝ => " (lean-expr Fn) ") _ x at h\n"
     "  convert h using 1\n"
     "  try simp only [id_eq, Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Real.sqrt_eq_rpow]\n"
     "  try ring_nf at *\n"
     "  try have hs := Real.sin_sq_add_cos_sq x\n"
     "  all_goals first\n"
     "    | (ring; done)\n"
     "    | (ring_nf; done)\n"
     "    | (ring_nf; ring; done)\n"
     "    | (norm_num; done)\n"
     "    | (nlinarith [Real.sin_sq_add_cos_sq x]; done)\n"
     "    | (ring_nf; nlinarith [Real.sin_sq_add_cos_sq x]; done)\n"
     "    | (linear_combination ((2 : ℝ) / 3 * Real.sin x) * hs; done)\n"
     "    | (linear_combination ((2 : ℝ) / 3 * Real.cos x) * hs; done)\n"
     "    | (simp only [mul_assoc, ← Real.rpow_add (by positivity)]; done)\n"
     "    | (ring_nf; rw [← Real.rpow_add (by positivity)]; norm_num; ring; done)\n"
     "    | (rw [← Real.rpow_neg (le_of_lt (by positivity))]; ring_nf; rw [← Real.rpow_add (by positivity)]; norm_num; ring; done)\n"
     "    | (nth_rewrite 1 [← Real.rpow_one x]; rw [← Real.rpow_add (by positivity)]; norm_num; done)\n"
     "    | (field_simp (discharger := positivity); ring; done)\n"
     "    | (field_simp (discharger := nlinarith); ring; done)\n"
     "    | (field_simp [" hnames "]; ring_nf; done)\n"
     "    | (field_simp; ring_nf; done)\n"
     ; rpow-половина: две формы обратной степени (a^(−1/2) и (a^(1/2))⁻¹) приводим к одной
     "    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_neg_half_inv]; field_simp (discharger := qedra_discharge); ring; done)\n"
     "    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_neg_half_inv]; field_simp (discharger := qedra_discharge); done)\n"
     "    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_neg_half_inv]; done)\n"
     ; s², s³ и пара s·s⁻¹ внутри произведения — сворачиваем и добиваем ring
     "    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_half_sq, qedra_rpow_half_cube, qedra_rpow_half_mul]; ring; done)\n"
     "    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_half_sq, qedra_rpow_half_mul]; ring; done)\n"
     "    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_half_mul, qedra_rpow_half_sq]; done)\n"
     ; то же с делением: a^(−1/2) → a^(1/2)/a, поле очищаем field_simp, произведения — снова в квадраты
     "    | (simp (discharger := qedra_discharge) only [mul_assoc, ← sq, qedra_rpow_half_neg, qedra_rpow_half_sq]; field_simp (discharger := qedra_discharge); simp (discharger := qedra_discharge) only [← sq, qedra_rpow_half_sq]; ring; done)\n"
     ; «x⁻¹»: поле очищаем, x ≠ 0 берём из разложенной гипотезы о знаменателе
     "    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_half_sq, qedra_rpow_half_mul]; field_simp (discharger := qedra_discharge); ring; done)\n"
     ; тригонометрическая цель после очистки поля: sin² + cos² = 1
     "    | (field_simp (discharger := qedra_discharge); nlinarith [Real.sin_sq_add_cos_sq x]; done)\n"
     ; √(1+x²): после field_simp нужен ring_nf (раскрыть произведения), затем s² = a и s³ = a·s
     "    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_neg_half_inv]; field_simp (discharger := qedra_discharge); ring_nf; simp (discharger := qedra_discharge) only [← sq, qedra_rpow_half_sq, qedra_rpow_half_cube]; ring; done)\n"
     "    | (simp (discharger := qedra_discharge) only [mul_assoc, qedra_rpow_neg_half_inv]; field_simp (discharger := qedra_discharge); ring_nf; simp (discharger := qedra_discharge) only [← sq, qedra_rpow_half_sq, qedra_rpow_half_cube]; done)\n"
     ; страж пустых теорем: только когда кроме x нет параметров (свидетеля для них не подобрать)
     (if (null? vars)
         (lean-vacuity-example id hyps x)
         ""))))

(define (lean-emit-antiderivative f F x conditions &rest rest)
  (let* ((id (if (null? rest) "antiderivative" (to-string (car rest))))
         (fn (lean-normalize f))
         (Fn (lean-normalize F))
         (bad (or (lean-bad-head fn) (lean-bad-head Fn))))
    (if bad
        (list 'unsupported (lean-unsupported-reason bad))
        (let ((ce (lean-conditions-entries (lean-list-of-conditions conditions) '())))
          (if (equal? (car ce) 'unsupported)
              ce
              (let* ((hyps0 (cadr ce))
                     (hyps (lean-collect-hyps Fn x (lean-collect-hyps fn x hyps0)))
                     (vars (sort (lean-collect-vars fn (lean-collect-vars Fn '()))
                                 (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
                     (conds (map lean-cond-core (lean-list-of-conditions conditions))))
                (lean-theorem-text id f F fn Fn x conds vars hyps)))))))

; ----- хеш текста .lean (полиномиальный, UTF-16; одинаков в Lisp и в сборщике результатов) -----

(define lean-alphabet
  (string-append " !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`"
                 "abcdefghijklmnopqrstuvwxyz{|}~\n\tℝ≠≤≥∧∨¬⁻¹π→·×…"))

(define (lean-hash s)
  (let loop ((i 0) (h 0))
    (if (>= i (string-length s))
        (string-append (number->string (string-length s)) "-" (number->string h))
        (let* ((c (string-ref s i))
               (k (string-index lean-alphabet c))
               (v (if k (+ k 1) 250)))
          (loop (+ i 1) (modulo (+ (* h 131) v) 4294967296))))))

; ----- приём результатов Lean (LEAN.L3): записи по хешу текста .lean -----

(define lean-results '())
(define lean-results-loaded #f)

(define (lean-results-add hash status file lemma toolchain log)
  (begin
    (set! lean-results (cons (list hash status file lemma toolchain log) lean-results))
    (set! lean-results-loaded #t)
    #t))

(define (lean-results-clear)
  (begin (set! lean-results '()) (set! lean-results-loaded #f) #t))

(define (lean-results-count) (length lean-results))

(define (lean-result-for source)
  (let ((h (lean-hash source)))
    (let loop ((rs lean-results))
      (cond ((null? rs) #f)
            ((equal? (car (car rs)) h) (car rs))
            (else (loop (cdr rs)))))))

; статус по тексту .lean: запись с тем же хешем либо not-run
(define (lean-status source)
  (let ((r (lean-result-for source)))
    (if r
        (list (cons 'status (nth r 1)) (cons 'file (nth r 2)) (cons 'lemma (nth r 3))
              (cons 'toolchain (nth r 4)) (cons 'log (nth r 5)))
        (list (cons 'status "not-run") (cons 'file "") (cons 'lemma "")
              (cons 'toolchain lean-toolchain) (cons 'log "")))))

; сертификат для MCP: source + статус (generated, если результаты ещё не принимались)
(define (lean-certificate f F x conditions)
  (let ((res (lean-emit-antiderivative f F x conditions "antiderivative")))
    (if (string? res)
        (let ((st (lean-status res)))
          (cons (cons 'source res)
                (if (equal? (cdr (assoc 'status st)) "not-run")
                    (if lean-results-loaded st (cons (cons 'status "generated") (cdr st)))
                    st)))
        (list (cons 'status "unsupported")
              (cons 'reason (if (pair? res) (cadr res) "ответ не переводится"))
              (cons 'source "") (cons 'file "") (cons 'lemma "")
              (cons 'toolchain lean-toolchain) (cons 'log "")))))
