; trigsimp.lisp — финальная тригонометрическая нормализация (шаг N1).
; НЕ входит в общий simplify (прежде тысячи ответов не меняются): вызывается явно (trigsimp e) и в
; финальной доводке ответов integrate (int-final, api.lisp). Значения не меняются: перестановки
; sin²+cos²=1 и следствия, выбор варианта с меньшим размером дерева.
;
; Идея: сформировать кандидатов (замена cos²u ↔ 1−sin²u, sin²u ↔ 1−cos²u, свёртка разности/суммы
; четвёртых степеней, expand), каждый нормировать (expand + simplify), взять вариант с меньшим
; числом узлов; повторять, пока размер уменьшается.
(module trigsimp
  (export trigsimp trigsimp-size trigsimp-half-angle))

; число узлов дерева выражения (размер — критерий выбора варианта)
(define (trigsimp-size e)
  (cond ((op-expr? e) (+ 1 (foldl (lambda (a s) (+ a (trigsimp-size s))) 0 (cdr e))))
        ((pair? e) (+ 1 (trigsimp-size (car e)) (trigsimp-size (cdr e))))
        (else 1)))

; суммарная степень sin/cos (N1: при равном размере предпочесть меньшие степени — «привычнее»)
(define (trigsimp-degree e)
  (cond ((and (op-expr? e) (equal? (car e) '^) (= (length e) 3) (op-expr? (cadr e))
              (member? (car (cadr e)) '(sin cos)) (real-numeric? (caddr e)))
         (if (> (caddr e) 1) (caddr e) 0))
        ((op-expr? e) (foldl (lambda (a s) (+ a (trigsimp-degree s))) 0 (cdr e)))
        ((pair? e) (+ (trigsimp-degree (car e)) (trigsimp-degree (cdr e))))
        (else 0)))

; лексикографическое качество: (размер, триг-степень) — меньше — лучше
(define (trigsimp-better? a b)
  (if (= (cdr a) (cdr b))
      (< (trigsimp-degree (car a)) (trigsimp-degree (car b)))
      (< (cdr a) (cdr b))))

; заменить все (^ (which u) 2) на 1 − (другая)^2: which='cos → 1 − sin²u, which='sin → 1 − cos²u
(define (trigsimp-replace e which)
  (cond ((and (op-expr? e) (equal? (car e) '^) (= (length e) 3)
              (op-expr? (cadr e)) (equal? (car (cadr e)) which) (equal? (caddr e) 2))
         (let ((u (cadr (cadr e))))
           (if (equal? which 'cos)
               (list '+ 1 (list '* -1 (list '^ (list 'sin u) 2)))
               (list '+ 1 (list '* -1 (list '^ (list 'cos u) 2))))))
        ((op-expr? e) (cons (car e) (map (lambda (a) (trigsimp-replace a which)) (cdr e))))
        (else e)))

; есть ли (^ (which u) 2) в дереве
(define (trigsimp-has-square e which)
  (cond ((and (op-expr? e) (equal? (car e) '^) (= (length e) 3)
              (op-expr? (cadr e)) (equal? (car (cadr e)) which) (equal? (caddr e) 2)) #t)
        ((op-expr? e) (any? (lambda (a) (trigsimp-has-square a which)) (cdr e)))
        (else #f)))

; из слагаемого t: числовой коэффициент при четвёртой степени тригонометрии или #f
(define (trigsimp-coef t)
  (cond ((and (op-expr? t) (equal? (car t) '*) (real-numeric? (cadr t))) (cadr t))
        ((and (op-expr? t) (equal? (car t) '^) (op-expr? (cadr t))
              (member? (car (cadr t)) '(sin cos)) (equal? (caddr t) 4)) 1)
        (else #f)))
; тело слагаемого (сам множитель-степень) или #f
(define (trigsimp-body t)
  (cond ((and (op-expr? t) (equal? (car t) '*) (real-numeric? (cadr t)) (= (length t) 3)) (caddr t))
        ((and (op-expr? t) (equal? (car t) '^) (op-expr? (cadr t))
              (member? (car (cadr t)) '(sin cos)) (equal? (caddr t) 4)) t)
        (else #f)))

; поиск в rs парного слагаемого −k·(h2 u)^4 → (парное . остальные) или #f
(define (trigsimp-pow4-find rs h2 u k)
  (if (null? rs) #f
      (let* ((t2 (car rs)) (k2 (trigsimp-coef t2)) (body2 (trigsimp-body t2)))
        (if (and k2 body2 (op-expr? body2) (= (length body2) 3) (equal? (car body2) '^)
                 (equal? (caddr body2) 4) (op-expr? (cadr body2))
                 (equal? (car (cadr body2)) h2)
                 (equal? (cadr (cadr body2)) u)
                 (equal? (- 0 k2) k))
            (cons t2 (cdr rs))
            (trigsimp-pow4-find (cdr rs) h2 u k)))))

; t = k·(h u)^4 и парное слагаемое −k·(h2 u)^4 (h2 — другая тригонометрия, тот же аргумент u) →
; k·(h²u − h2²u)(h²u + h2²u); сумма квадратов сворачивается simplify → 1, остаётся k·(h²u − h2²u)
(define (trigsimp-pow4-match t rest)
  (and (op-expr? t)
       (let ((k (trigsimp-coef t)) (body (trigsimp-body t)))
         (and k body (op-expr? body) (= (length body) 3) (equal? (car body) '^)
              (equal? (caddr body) 4) (op-expr? (cadr body))
              (member? (car (cadr body)) '(sin cos))
              (let* ((u (cadr (cadr body))) (h (car (cadr body)))
                     (h2 (if (equal? h 'sin) 'cos 'sin)))
                (trigsimp-pow4-find rest h2 u k))))))


; свернуть в сумме все пары ±k·четвёртых степеней (terms — оставшиеся слагаемые, out — накопленные)
(define (trigsimp-pow4-go terms out)
  (if (null? terms)
      (cons '+ (reverse out))
      (let ((t (car terms)) (rest (cdr terms)))
        (let ((pair (trigsimp-pow4-match t rest)))
          (if pair
              (let* ((k (trigsimp-coef t)) (b (trigsimp-body t)) (u (cadr (cadr b)))
                     (h (car (cadr b))) (h2 (if (equal? h 'sin) 'cos 'sin))
                     (s2 (list '^ (list h u) 2)) (c2 (list '^ (list h2 u) 2)))
                ; k·(h²−h2²)·(h²+h2²): k внутрь разности — иначе внешний множитель −1 блокирует
                ; свёртку суммы квадратов в 1; после simplify остаётся k·(h²−h2²)
                (trigsimp-pow4-go (cdr pair)
                                  (cons (list '* (list '- (list '* k s2) (list '* k c2))
                                             (list '+ s2 c2)) out)))
              (trigsimp-pow4-go rest (cons t out)))))))

(define (trigsimp-pow4-diff e)
  (if (not (and (op-expr? e) (equal? (car e) '+))) e
      (trigsimp-pow4-go (cdr e) '())))

; делится ли слагаемое на квадрат m = (^ (h u) 2) → множитель-частное или #f
; (* k m rest...) → (* k rest...); само m → 1; (^ (h u) 4) → (^ (h u) 2); m·(произведение без чисел) → частное
(define (trigsimp-div-square t h u)
  (let ((m (list '^ (list h u) 2)) (one? (equal? t (list '^ (list h u) 2)))
        (p4 (and (op-expr? t) (equal? (car t) '^) (= (length t) 3)
                 (op-expr? (cadr t)) (equal? (car (cadr t)) h) (equal? (cadr (cadr t)) u)
                 (equal? (caddr t) 4))))
    (cond (one? 1)
          (p4 (list '^ (list h u) 2))
          ((and (op-expr? t) (equal? (car t) '*))
           (let ((fac (map (lambda (f) (if (equal? f m) #t f)) (cdr t))))
             (if (member? #t fac)
                 (let ((rest (filter (lambda (f) (not (equal? f #t))) fac)))
                   (cond ((null? rest) 1)
                         ((and (= (length rest) 1)) (car rest))
                         (else (cons '* rest))))
                 #f)))
          (else #f))))

; кандидат: вынести общий тригонометрический квадрат из всех слагаемых суммы
; (после simplify скобка часто сворачивается по тождеству: s²c² + c⁴ → c²(s²+c²) → c²)
; sqs — список кандидатов (h u); → (* (^ (h u) 2) сумма-частных) или #f
(define (trigsimp-factor-try sqs terms)
  (if (null? sqs) #f
      (let* ((h (car (car sqs))) (u (cadr (car sqs)))
             (qs (map (lambda (t) (trigsimp-div-square t h u)) terms)))
        (if (every? (lambda (q) q) qs)
            (list '* (list '^ (list h u) 2)
                  (if (= (length qs) 1) (car qs) (cons '+ qs)))
            (trigsimp-factor-try (cdr sqs) terms)))))

(define (trigsimp-factor-square e)
  (if (not (and (op-expr? e) (equal? (car e) '+) (> (length e) 2))) #f
      (trigsimp-factor-try (trigsimp-squares-of (cadr e)) (cdr e))))

; все (^ (h u) 2) слагаемого (h u) — кандидаты на общий множитель
(define (trigsimp-squares-of t)
  (cond ((and (op-expr? t) (equal? (car t) '^) (= (length t) 3) (op-expr? (cadr t))
              (member? (car (cadr t)) '(sin cos)) (equal? (caddr t) 2))
         (list (list (car (cadr t)) (cadr (cadr t)))))
        ((and (op-expr? t) (equal? (car t) '^) (= (length t) 3) (op-expr? (cadr t))
              (member? (car (cadr t)) '(sin cos)) (equal? (caddr t) 4))
         (list (list (car (cadr t)) (cadr (cadr t)))))
        ((and (op-expr? t) (member? (car t) '(* +)))
         (append-map trigsimp-squares-of (cdr t)))
        (else '())))

; кандидаты следующего шага из e
(define (trigsimp-candidates e)
  (let ((cs (list (trigsimp-pow4-diff e) (expand e))))
    (let ((fs (trigsimp-factor-square e)))
      (if fs (set! cs (cons fs cs))))
    (if (trigsimp-has-square e 'cos)
        (set! cs (cons (trigsimp-replace e 'cos) cs)))
    (if (trigsimp-has-square e 'sin)
        (set! cs (cons (trigsimp-replace e 'sin) cs)))
    cs))

; нормировка кандидата: expand → simplify (сбор подобных — движок)
(define (trigsimp-norm e) (simplify (expand e)))

; (trigsimp e) — лучшая тригонометрическая форма e: качество = (размер, суммарная степень sin/cos),
; лексикографически меньше — лучше; итеративно, пока улучшается (строгие < — guard от зацикливания)
(define (trigsimp-go e best-size best-deg)
  (let* ((cands (filter (lambda (c) (not (equal? c e))) (trigsimp-candidates e)))
         (normed (map trigsimp-norm cands))
         (mk (lambda (n) (cons n (trigsimp-size n))))
         (pairs (map mk normed))
         (imp (filter (lambda (p) (or (< (cdr p) best-size)
                                       (and (= (cdr p) best-size)
                                            (< (trigsimp-degree (car p)) best-deg))))
                      pairs)))
    (if (null? imp)
        e
        (let ((m (foldl (lambda (a p) (if (trigsimp-better? p a) p a)) (car imp) imp)))
          (trigsimp-go (car m) (cdr m) (trigsimp-degree (car m)))))))

(define (trigsimp e0)
  (let* ((e (simplify e0)))
    (trigsimp-go e (trigsimp-size e) (trigsimp-degree e))))
; --- Половинные углы (N1, только внутри log/atan финальной доводки integrate) ---
; (1 − cos u)·(sin u)⁻¹ → tan(u/2);  (1 + cos u)·(sin u)⁻¹ → 1/tan(u/2); u — общий аргумент.
; Работает на произведениях (* ... (±1 ± cos u) ... (^ (sin u) -1) ...); прочие множители сохраняются

; множитель ±1 ± cos u → ('minus|'plus u) или #f
(define (trigsimp-one-cos f)
  (and (op-expr? f) (equal? (car f) '+) (= (length f) 3)
       (let ((a (cadr f)) (b (caddr f)))
         (cond ((and (equal? a 1) (op-expr? b) (equal? (car b) '*) (real-numeric? (cadr b))
                     (equal? (cadr b) -1) (op-expr? (caddr b)) (equal? (car (caddr b)) 'cos))
                (list 'minus (cadr (caddr b))))
               ((and (equal? a 1) (op-expr? b) (equal? (car b) 'cos))
                (list 'plus (cadr b)))
               (else #f)))))

; произведение с (1±cos u) и (^ (sin u) -1) → форма половинного угла или #f
(define (trigsimp-half-prod e)
  (and (op-expr? e) (equal? (car e) '*)
       (let ((oc #f) (sn #f) (rest '()))
         (map (lambda (f)
                     (let ((c (trigsimp-one-cos f)))
                       (cond (c (if (not oc) (set! oc c)))
                             ((and (op-expr? f) (equal? (car f) '^) (= (length f) 3)
                                   (op-expr? (cadr f)) (equal? (car (cadr f)) 'sin)
                                   (equal? (caddr f) -1))
                              (set! sn (cadr (cadr f))))
                             (else (set! rest (cons f rest))))))
                    (cdr e))
         (and oc sn (equal? (cadr oc) sn)
              (let ((half (list 'tan (list '* 1/2 sn)))
                    (tail (reverse rest)))
                (if (equal? (car oc) 'minus)
                    (if (null? tail) half (cons '* (cons half tail)))
                    ; (1+cos u)/sin u → cot(u/2) — именно cot (не 1/tan): упрощатель печати log/atan
                    ; не развернёт его (см. m-simp в mathlang/runtime.lisp, шаг N1)
                    (let ((ct (list (quote cot) (list (quote *) 1/2 sn))))
                      (if (null? tail) ct (cons (quote *) (cons ct tail))))))))))
; заменить формы половинных углов внутри аргумента (рекурсивно по поддереву)
(define (trigsimp-half-in arg)
  (let ((p (trigsimp-half-prod arg)))
    (if p p
        (if (op-expr? arg)
            (cons (car arg) (map trigsimp-half-in (cdr arg)))
            arg))))

; финальная свёртка половинных углов: только внутри log и atan (вне — остальная математика не меняется)
(define (trigsimp-half-angle e)
  (cond ((and (op-expr? e) (member? (car e) '(log atan)) (= (length e) 2))
         (list (car e) (trigsimp-half-in (cadr e))))
        ((op-expr? e) (cons (car e) (map trigsimp-half-angle (cdr e))))
        (else e)))
