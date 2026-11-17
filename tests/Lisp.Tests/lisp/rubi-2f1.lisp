; RUBI.2F1: ответы Rubi через ₂F₁ и F₁ Аппеля (598 невзятых задач research/rubi/hyp-notok.tsv).
; Две причины: (1) GtQ/LtQ/GeQ/LeQ (IUF.m:403-471) — N[Together[u]]: b/(b·bc/(bc−ad) − a·bd/(bc−ad)) = 1 > 0, а порт
; сравнивал только числа и константы, поэтому правила 1.1.1.3 #70/#72 с буквенными m, n, p не срабатывали после
; приведения к (bc/(bc−ad) + bd x/(bc−ad)); (2) проверка ответа с appell-f1/hypergeometric-2f1 брала одни и те же
; положительные параметры — аргументы F₁ попадали на разрез [1, ∞) или вне круга сходимости, eval-num отказывал
; (skip:heads). Теперь запасная проверка берёт псевдослучайные параметры (rubi-hyp2-check).

(define (f2-near? a b tol)
  (and (number? a) (number? b) (<= (abs (- a b)) (* tol (+ 1 (abs b))))))

(define (f2-integrate s)
  (let ((old rubi::rubi-time-limit))
    (unwind-protect
      (begin (set! rubi::rubi-time-limit 60.0)
             (rubi-integrate (math-read s) 'x))
      (set! rubi::rubi-time-limit old))))

; независимая проверка: центральная разность самого F (а не формальная производная) против f; параметры — набор k
(define (f2-vals ps k)
  (let numbered ((rest ps) (i 0) (acc '()))
    (if (null? rest) (reverse acc)
        (numbered (cdr rest) (+ i 1)
                  (cons (list (car rest) (/ (+ 11 (modulo (* (+ i 3) (+ k 5) 7) 19)) 10)) acc)))))

(define (f2-antiderivative? F f)
  (let* ((ps (integrate::int-symbols (list '+ F f) 'x))
         (verdicts (append-map (lambda (k)
                                 (let ((vals (f2-vals ps k)))
                                   (map (lambda (p) (integrate::int-F-point-verdict F f 'x p vals)) '(1/10 1/5 3/10))))
                               '(0 1 2))))
    (and (not (member? 'bad verdicts)) (not (member? 'gross verdicts))
         (>= (length (filter (lambda (v) (equal? v 'ok)) verdicts)) 3))))

(deftest "rubi-2f1/1: GtQ через Together — число из символьного выражения"
  (assert-true (rubi::rubi-gtq '(/ b (- (* b (/ (* b c) (- (* b c) (* a d)))) (* a (/ (* b d) (- (* b c) (* a d)))))) 0))
  (assert-true (not (rubi::rubi-gtq '(/ b a) 0)))
  (assert-true (not (rubi::rubi-gtq 'a 0)))
  (assert-true (rubi::rubi-ltq '(- (/ 1 (+ 1 1))) 0)))

(deftest "rubi-2f1/2: ∫(a+bx)^m (c+dx)^n/(e+fx) — F₁ Аппеля с буквенными показателями"
  (let* ((s "(a + b*x)**m*(c + d*x)**n/(e + f*x)")
         (f (math-read s))
         (r (f2-integrate s)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (rubi::rubi-has-head? r 'appell-f1))
    (assert-true (f2-antiderivative? r (simplify f)))))

(deftest "rubi-2f1/3: подделки ответа F₁ отвергаются (×1.001, −F, +x, сдвиг параметра c, смена показателя)"
  (let* ((s "(a + b*x)**m*(c + d*x)**n/(e + f*x)")
         (f (math-read s))
         (r (f2-integrate s)))
    (assert-true (rubi::rubi-int-check-search r f 'x))
    (assert-true (not (rubi::rubi-int-check-search (list '* 1001/1000 r) f 'x)))
    (assert-true (not (rubi::rubi-int-check-search (list '* -1 r) f 'x)))
    (assert-true (not (rubi::rubi-int-check-search (list '+ r 'x) f 'x)))
    ; сдвиг четвёртого параметра (c) у каждого appell-f1
    (let ((shift (lambda (self u)
                   (cond ((not (pair? u)) u)
                         ((equal? (car u) 'appell-f1)
                          (list 'appell-f1 (nth u 1) (nth u 2) (nth u 3) (list '+ (nth u 4) 1) (nth u 5) (nth u 6)))
                         (else (cons (car u) (map (lambda (v) (self self v)) (cdr u))))))))
      (assert-true (not (rubi::rubi-int-check-search (shift shift r) f 'x))))
    ; другой подынтеграл: ответ на ∫(...)/(e+fx) не принимается за ответ на (...)·(e+fx)^2
    (assert-true (not (rubi::rubi-int-check-search r (math-read "(a + b*x)**m*(c + d*x)**n*(e + f*x)") 'x)))))

(deftest "rubi-2f1/4: ∫(a + b sin(c+dx))^n — ответ через F₁ принимается проверкой при параметрах со знаками"
  (let* ((s "(a + b*sin(c + d*x))**n")
         (f (math-read s))
         (r (f2-integrate s)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (f2-antiderivative? r (simplify f)))
    (assert-true (not (rubi::rubi-int-check-search (list '* 1001/1000 r) f 'x)))
    (assert-true (not (rubi::rubi-int-check-search (list '+ r (list '* 1/10 'x)) f 'x)))))

(deftest "rubi-2f1/5: честный отказ — ответ с главной ветвью, не являющийся первообразной, не принимается"
  ; Rubi 1.2.1.2 #133: (a+bx+cx²)^(4/3)/(d+ex)² — формула через (−1/(d+ex))^(8/3) · (1/(d+ex))^(−5/3) на главных
  ; ветвях отличается от первообразной постоянным множителем e^(−iπ/3); проверка вправе (и обязана) отвергнуть
  (let ((r (f2-integrate "(a + b*x + c*x**2)**(4/3)/(d + e*x)**2")))
    (assert-true (or (equal? r 'unknown)
                     (f2-antiderivative? r (simplify (math-read "(a + b*x + c*x**2)**(4/3)/(d + e*x)**2")))))))
