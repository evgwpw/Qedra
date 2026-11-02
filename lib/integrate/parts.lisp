; integrate/parts.lisp — интегрирование по частям (LIATE) и раскрытие скобок (часть бывшего lib\integrate.lisp, шаг 21h').
; Регистрирует стратегии int-parts, int-expand. Загружается после integrate/trig.lisp.
(module integrate)

; ---------- интегрирование по частям (LIATE) ----------
; ∫ u dv = u·v − ∫ v du; u выбирается по LIATE: логарифм (1), обратные тригонометрические (2), многочлены/степени x (3),
; тригонометрические (4), показательные (5); степени x с отрицательным/дробным показателем — ранг 6 (хуже показательных).
; Одиночный множитель ранга 1–2 (log x ^ k, atan(x²)): u = e, dv = dx. Повтор — через рекурсию каскада (глубина < int-max-depth).
; Циклический случай (exp·sin, exp·cos): после двух шагов e3 = c·e (c без x) ⇒ I = (P1 − P2)/(1 − c).

(define (int-rank f x)
  (cond ((x-free? f x) 0)
        ((not (op-expr? f)) 3)
        ((equal? (car f) 'log) 1)
        ((member? (car f) '(asin acos atan acot asec acsc asinh acosh atanh acoth)) 2)
        ((member? (car f) '(sin cos tan cot sec csc sinh cosh tanh coth sech csch)) 4)
        ((equal? (car f) 'exp) 5)
        ((equal? (car f) '^)
         (cond ((x-free? (cadr f) x) 5)
               ((not (x-free? (caddr f) x)) 7)
               ((polynomial? (cadr f) x) (if (and (integer? (caddr f)) (> (caddr f) 0)) 3 6))
               (else (int-rank (cadr f) x))))
        ((polynomial? f x) 3)
        (else 6)))

(define (int-min-rank-factor fs x)
  (foldl (lambda (best f) (if (< (int-rank f x) (int-rank best x)) f best)) (car fs) (cdr fs)))

; e → (u dv) или #f
(define (int-remove-first u l)
  (cond ((null? l) '())
        ((equal? (car l) u) (cdr l))
        (else (cons (car l) (int-remove-first u (cdr l))))))

(define (int-liate-split e x)
  (let* ((all (if (and (op-expr? e) (equal? (car e) '*)) (cdr e) (list e)))
         (fs (filter (lambda (f) (not (x-free? f x))) all)))   ; множители без x — только в dv
    (cond ((null? fs) #f)
          ((null? (cdr fs))
           (and (<= (int-rank (car fs) x) 2)
                (list (car fs) (simplify (cons '* (cons 1 (int-remove-first (car fs) all)))))))
          (else
           (let ((u (int-min-rank-factor fs x)))
             (and (<= (int-rank u x) 5)
                  (list u (simplify (cons '* (cons 1 (int-remove-first u all)))))))))))

; один шаг: (P e2): P = u·v, e2 = v·u'. Шаг S.4, порядок как в учебнике: шаг int-parts-choice («Выбор u и dv»; внутри —
; вложенный шаг нахождения v = ∫ dv), затем int-parts-formula: ∫ e dx = P − ∫ e2 dx
(define (int-dx-sym x) (string->symbol (string-append "d" (to-string (int-p x)))))
(define (int-dv-form dv x) (if (equal? dv 1) (int-dx-sym x) (list '* (int-p dv) (int-dx-sym x))))

(define (int-parts-step e u dv x d)
  (let* ((du (int-diff x u))
         (v (with-step ('int-parts-choice "Выбор u и dv" (int-form e x)
                         :comment (lambda (v) (string-append "по правилу LIATE; du = " (int-mp (simplify du)) " dx; v = ∫ dv = " (int-mp v)
                                                             " (вложенный шаг ниже)"))
                         :after (lambda (v) (list 'list (list '= 'u (int-p u)) (list '= 'dv (int-dv-form dv x)))))
              (int-go dv x (+ d 1)))))
    (and v (let ((st (list (simplify (list '* u v)) (simplify (list '* v du)))))
             (if (step-log-enabled?)
                 (record-step 'int-parts-formula "Формула интегрирования по частям"
                              (string-append "∫ u dv = u·v − ∫ v du; здесь u = " (int-mp u) ", v = " (int-mp v) ", du = "
                                             (int-mp (simplify du)) " dx")
                              (int-form e x)
                              (list '+ (int-p (car st)) (list '* -1 (int-form (cadr st) x)))))
             st))))

(define (int-cyclic? e x)
  (let ((fs (filter (lambda (f) (not (x-free? f x))) (if (and (op-expr? e) (equal? (car e) '*)) (cdr e) (list e)))))
    (and (> (length fs) 1)
         (every? (lambda (f) (member? (int-rank f x) '(4 5))) fs)
         (any? (lambda (f) (= (int-rank f x) 4)) fs)
         (any? (lambda (f) (= (int-rank f x) 5)) fs))))

(define (int-parts-cyclic e x d)
  (let ((s1 (int-liate-split e x)))
    (and s1
         (let ((st1 (int-parts-step e (car s1) (cadr s1) x d)))
           (and st1
                (let ((s2 (int-liate-split (cadr st1) x)))
                  (and s2
                       (let ((st2 (int-parts-step (cadr st1) (car s2) (cadr s2) x d)))
                         (and st2
                              (let ((c (simplify (list '* (cadr st2) (list '^ e -1)))))
                                (and (x-free? c x) (not (equal? c 1))
                                     (let ((res (simplify (list '* (list '^ (list '+ 1 (list '* -1 c)) -1)
                                                                (list '+ (car st1) (list '* -1 (car st2)))))))
                                       (if (step-log-enabled?)
                                           (record-step 'int-parts-cycle "Циклический случай: решаем уравнение относительно интеграла"
                                                        (string-append "после двух шагов ∫ f dx = P1 − P2 + c·∫ f dx, c = " (int-mp c)
                                                                       "; ∫ f dx = (P1 − P2)/(1 − c)")
                                                        (int-form e x) (int-p res)))
                                       res))))))))))))

; чисто тригонометрическое произведение/степень (все множители с x — ранг 4, не меньше двух): по частям раздувает
; ветвление до минут (sin²x·cos 3x ≈ 15 с и невычисленно) — этим занимаются int-trig/int-prodsum
(define (int-pure-trig-product? e x)
  (and (op-expr? e) (equal? (car e) '*)
       (let ((fs (filter (lambda (f) (not (x-free? f x))) (cdr e))))
         (and (> (length fs) 1) (every? (lambda (f) (= (int-rank f x) 4)) fs)))))

(define (int-parts e x d)
  (and (< d int-max-depth)
       (not (int-pure-trig-product? e x))
       (or (and (int-cyclic? e x)
                (with-step ('int-by-parts "Интегрирование по частям (циклический случай)" (int-form e x)
                            :comment "по частям дважды: исходный интеграл возвращается с множителем c, получаем уравнение" :after int-p)
                  (int-parts-cyclic e x d)))
           (let ((s (int-liate-split e x)))
             (and s
                  (with-step ('int-by-parts "Интегрирование по частям" (int-form e x)
                              :comment "∫ u dv = u·v − ∫ v du; u выбирается по правилу LIATE (логарифм, обратная тригонометрия, алгебраическая, тригонометрия, показательная)"
                              :after int-p)
                    (let ((st (int-parts-step e (car s) (cadr s) x d)))
                      (and st
                           (let ((r (int-go (cadr st) x (+ d 1))))
                             (if r (simplify (list '+ (car st) (list '* -1 r))) (begin (attempt-fail "интеграл v·du не берётся (по частям не сходится)") #f)))))))))))

(int-add-strategy int-parts)

; ---------- раскрытие скобок (последний шанс) ----------
(define (int-expand e x d)
  (and (< d 3) (op-expr? e)
       (or (and (equal? (car e) '*) (any? (lambda (f) (and (op-expr? f) (equal? (car f) '+))) (cdr e)))
           (and (equal? (car e) '^) (op-expr? (cadr e)) (equal? (car (cadr e)) '+) (integer? (caddr e)) (> (caddr e) 1)))
       (let ((ex (expand e)))
         (and (not (equal? ex e))
              (with-step ('int-expand "Раскрытие скобок в подынтегральной функции" (int-form e x)
                          :comment "раскрываем скобки и интегрируем получившуюся сумму" :after int-p)
                (begin
                  (if (step-log-enabled?)
                      (record-step 'int-expand-brackets "Раскрытие скобок" "" (int-form e x) (int-form ex x)))
                  (let ((r (int-go ex x (+ d 1)))) (if r r (begin (attempt-fail "раскрытая сумма не интегрируется") #f)))))))))

(int-add-strategy int-expand)
