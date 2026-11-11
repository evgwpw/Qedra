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
                 ((equal? h '^) (lean-power (car args) (caddr e)))
                 ((equal? h 'sqrt) (string-append "Real.sqrt (" (car args) ")"))
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
        ((and (integer? n) (> n 0))
         (string-append "(" base " ^ " (number->string n) ")"))
        ((and (integer? n) (< n 0))
         (let ((k (- n)))
           (if (= k 1)
               (string-append "(" base "⁻¹)")
               (string-append "((" base "⁻¹) ^ " (number->string k) ")"))))
        (else (string-append "(" base " ^ " (lean-number-lit n) ")"))))

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

; автоматические гипотезы по дереву: знаменатель, log/sqrt/rpow, asin/acos
(define (lean-collect-hyps e x hyps)
  (cond ((or (not (pair? e)) (null? e)) hyps)
        ((equal? (car e) '/)
         (let ((num (cadr e)) (den (caddr e)))
           (lean-collect-hyps num x
             (lean-collect-hyps den x
               (lean-add-hyp (list '!= den 0) (lean-ne-type den) hyps)))))
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
             ((and (integer? n) (> n 0))
              (string-append "((" (lean-deriv-term b x hyps) ").pow " (number->string n) ")"))
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

(define (lean-theorem-text id f F fn Fn x conditions vars hyps)
  (let ((params (lean-param-list vars hyps))
        (hnames (lean-hyp-names hyps))
        (term (lean-deriv-term Fn x hyps)))
    (string-append
     "import Mathlib\n"
     "open Real\n"
     "\n"
     "-- qedra: integrate(" (math-print f) ", " (symbol->string x) ") -> " (math-print F)
     "; conditions: " (lean-conditions-comment conditions) "\n"
     "theorem qedra_int_" id (if (equal? params "") "" (string-append " " params)) " :\n"
     "    HasDerivAt (fun x : ℝ => " (lean-expr Fn) ") (" (lean-expr fn) ") x := by\n"
     "  have h := " term "\n"
     "  change HasDerivAt (fun x : ℝ => " (lean-expr Fn) ") _ x at h\n"
     "  convert h using 1\n"
     "  try simp only [id_eq, Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Real.sqrt_eq_rpow]\n"
     "  try ring_nf at *\n"
     "  all_goals first\n"
     "    | ring_nf\n"
     "    | ring_nf; try nlinarith [Real.sin_sq_add_cos_sq x]\n"
     "    | ring_nf; field_simp (discharger := nlinarith); try ring\n"
     "    | field_simp (discharger := nlinarith); try ring\n"
     "    | field_simp [" hnames "]; try ring_nf\n"
     "    | field_simp; try ring_nf\n")))

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
