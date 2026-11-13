; RUBI.ELL1: дефекты генератора/утилит Rubi, блокировавшие эллиптические ответы в 1.1.x (research/rubi/class2/ids.tsv).
; Источник семантики — Rubi 4.17.3.0 (commit 61e9c18, tools/rubi/src/IntegrationUtilityFunctions.m).
(load (string-append lib-dir "rubi/utils.lisp"))

; другие файлы тестов подменяют правила Rubi игрушечными наборами - возвращаем настоящие
(define (rell-fresh)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #f)
  (set! rubi::*rubi-stage* 0)
  (set! rubi::*rubi-bodies* (make-hash))
  (set! rubi::*rubi-bodies-loaded* (make-hash)))

(define (rell-body file id)
  (rubi::rubi-load-bodies file)
  (format "~s" (hash-ref rubi::*rubi-bodies* id #f)))

; численная сверка производной в точках разных знаков x (int-check смотрит только x > 0)
(define (rell-deriv-ok? f e pts)
  (equal? 'ok (integrate::int-numeric-status-at (list '- (integrate::int-diff 'x f) e) f 'x 0.000001 pts)))

; --- 1) Sqrt[n] целого литерала — точный радикал, а не алгебраическое число ---

(deftest "rubi-ell1/1: в телах правил нет (sqrt 3) — литерал вычислялся бы в root(...)"
  (rell-fresh)
  (assert-true (not (string-contains? (rell-body "1.1.3.7" "Rubi 1.1.3.7 #28") "(sqrt 3)")))
  (assert-true (string-contains? (rell-body "1.1.3.7" "Rubi 1.1.3.7 #28") "(^ 3 1/2)")))

(deftest "rubi-ell1/1: rubi-eqq на смеси с (^ 3 1/2) даёт #t (с (sqrt 3) было #f)"
  ; D^3 = 1/(2 (5 - 3 sqrt 3)): 1 - 2 (5 - 3 sqrt 3) D^3 = 0
  (let ((d '(^ (/ 1 (* 2 (- 5 (* 3 (^ 3 1/2))))) 1/3)))
    (assert-true (rubi::rubi-eqq (list '- 1 (list '* '(* 2 (- 5 (* 3 (^ 3 1/2)))) (list '^ d 3))) 0))
    (assert-true (not (rubi::rubi-eqq (list '- 2 (list '* '(* 2 (- 5 (* 3 (^ 3 1/2)))) (list '^ d 3))) 0)))))

(deftest "rubi-ell1/1: (x + 1 + sqrt 3)/sqrt(-x^3 - 1) берётся (1.1.3.8/81), ответ с elliptic-f, производная верна"
  (rell-fresh)
  (let* ((e (math-read "(x + 1 + sqrt(3))/sqrt(-x^3 - 1)"))
         (_ (set! rubi::rubi-time-limit 30.0))   ; под нагрузкой шардов бюджет 4 с мал (в покое ≈ 2,6 с)
         (r (rubi-integrate e 'x)))
    (set! rubi::rubi-time-limit 4.0)
    (assert-true (not (equal? r 'unknown)))
    (assert-true (rubi::rubi-has-head? r 'elliptic-f))
    ; подынтегральное вещественно при x < -1; ответ сверяем и там, и при x > -1 (комплексно — пропуск)
    (assert-true (rubi::rubi-int-check r e 'x))
    ; подделка против int-check: тот же ответ с лишним множителем отвергается
    (assert-true (not (rubi::rubi-int-check (list '* 2 r) e 'x)))))

; --- 2) equal? в правой части /; не теряет знак ? ---

(deftest "rubi-ell1/2: 1.1.3.7 #5 — (equal? q (- n 1)), а не (equal q ...)"
  (rell-fresh)
  (let ((s (rell-body "1.1.3.7" "Rubi 1.1.3.7 #5")))
    (assert-true (string-contains? s "(equal? q"))
    (assert-true (not (string-contains? s "(equal q")))))

; --- 3) a_ без точки в сумме не связывается с 0 ---

(deftest "rubi-ell1/3: в условии правила a_ + b_.*x^2 + c_.*x^4 есть a != 0"
  (rell-fresh)
  (assert-true (string-contains? (rell-body "1.2.2.2" "Rubi 1.2.2.2 #35") "(not (equal? ?a 0))")))

(deftest "rubi-ell1/3: (A + B x^2)/(b x^2 + c x^4)^(3/2) (1.1.4.3/156) — без 0^(-1), верно при x < 0 и x > 0"
  (rell-fresh)
  (let* ((e (math-read "(A + B*x^2)/(b*x^2 + c*x^4)^(3/2)"))
         (_ (set! rubi::rubi-time-limit 30.0))
         (r (rubi-integrate e 'x)))
    (set! rubi::rubi-time-limit 4.0)
    (assert-true (not (equal? r 'unknown)))
    (assert-true (rell-deriv-ok? r e '(-1.3 -0.45)))
    (assert-true (rell-deriv-ok? r e '(0.7 1.9)))
    (assert-true (not (rell-deriv-ok? (list '+ r 'x) e '(-1.3 -0.45))))))

; --- 4) ExpandIntegrand[u,v,x] = DistributeOverTerms[u, ExpandIntegrand[v,x], x] (IUF.m:3384) ---

(deftest "rubi-ell1/4: ExpandIntegrand[u,v,x] раскладывает v и распределяет u по слагаемым"
  (let ((r (rubi::rubi-expand-integrand '(^ (+ a (* c (^ x 4))) p)
                                        '(^ (- (/ d (- (^ d 2) (* (^ e 2) (^ x 4)))) (/ (* e (^ x 2)) (- (^ d 2) (* (^ e 2) (^ x 4))))) 1)
                                        'x)))
    ; сумма из двух слагаемых, у каждого множитель u — не произведение с множителем-суммой
    (assert-true (rubi::rubi-sumq r))
    (assert-equal 2 (length (cdr r)))
    (assert-true (every? (lambda (t) (equal? (car t) '*)) (cdr r)))))
