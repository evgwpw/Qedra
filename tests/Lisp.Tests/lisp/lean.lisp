; LEAN.L1/L2: генератор .lean — эталоны (10 файлов каталога), гипотезы, unsupported, хеш, приём результатов.

; Сравнение не должно зависеть от концов строк: на Windows git отдаёт файлы с CRLF, генератор пишет LF.
; В диалекте нет escape-последовательностей \r/\n (это два символа), поэтому сверяем построчно:
; строки равны, если совпадают или файловая длиннее ровно на один символ (CR) при совпадении префикса.
(define (lean-lines s) (string-split s (format "~%")))

(define (lean-line-ok? a b)
  (or (equal? a b)
      (and (= (string-length a) (+ (string-length b) 1))
           (equal? (substring a 0 (string-length b)) b))))

(define (lean-lines-same? la lb)
  (cond ((and (null? la) (null? lb)) #t)
        ((or (null? la) (null? lb)) #f)
        ((or (lean-line-ok? (car la) (car lb)) (lean-line-ok? (car lb) (car la)))
         (lean-lines-same? (cdr la) (cdr lb)))
        (else #f)))

; хвостовые пустые строки и строки из одного символа (CR при CRLF) не сравниваем
(define (lean-drop-tail l)
  (if (null? l)
      l
      (let ((r (reverse l)))
        (if (or (equal? (car r) "")
                (and (string? (car r)) (= (string-length (car r)) 1)))
            (lean-drop-tail (reverse (cdr r)))
            l))))

(define (lean-same? a b)
  (lean-lines-same? (lean-drop-tail (lean-lines a)) (lean-drop-tail (lean-lines b))))

(define (lean-file id) (read-text-file (string-append "lean/catalog/" id ".lean")))
(define (lean-check f F id)
  (let ((r (lean-emit-antiderivative f F 'x '() id)))
    (assert-true (string? r))
    (assert-true (lean-same? r (lean-file id)))))
(define (lean-out f F id) (lean-emit-antiderivative f F 'x '() id))
(define (lean-has? s part) (string-contains? s part))

; ---------- П1: 10 эталонов (текст сверяется с lean/catalog/<id>.lean) ----------

(deftest "lean: эталон x → x^2/2" (lean-check 'x '(* 1/2 (^ x 2)) "int_0001"))
(deftest "lean: эталон 1/x → log x" (lean-check '(/ 1 x) '(log x) "int_0004"))
(deftest "lean: эталон x*exp(x^2) → exp(x^2)/2" (lean-check '(* x (exp (^ x 2))) '(* 1/2 (exp (^ x 2))) "int_0006"))
(deftest "lean: эталон sin x → −cos x" (lean-check '(sin x) '(* -1 (cos x)) "int_0010"))
(deftest "lean: эталон tan x → −log(cos x)" (lean-check '(tan x) '(* -1 (log (cos x))) "int_0012"))
(deftest "lean: эталон sqrt x → 2/3 x^(3/2)" (lean-check '(sqrt x) '(* 2/3 (^ x 3/2)) "int_0014"))
(deftest "lean: эталон x^2*sin x" (lean-check '(* (^ x 2) (sin x)) '(+ (* -1 (^ x 2) (cos x)) (* 2 (+ (* x (sin x)) (cos x)))) "ref_x2sinx"))
(deftest "lean: эталон x*sin x" (lean-check '(* x (sin x)) '(+ (* -1 x (cos x)) (sin x)) "int_0019"))
(deftest "lean: эталон рациональный с atan" (lean-check '(/ 1 (+ (^ x 2) (* 2 x) 5)) '(* 1/2 (atan (* 1/2 (+ 1 x)))) "int_0035"))
(deftest "lean: эталон 1/(1+e^x)" (lean-check '(/ 1 (+ 1 (exp x))) '(+ x (* -1 (log (+ 1 (exp x))))) "int_0043"))

; ---------- П2: гипотезы §1.4 ----------

(deftest "lean: гипотеза знаменателя"
  (let ((s (lean-out '(/ 1 x) '(log x) "hyp-div")))
    (assert-true (lean-has? s "(h1 : x ≠ 0)"))))

(deftest "lean: гипотеза log — 0 < u (а не u ≠ 0)"
  (let ((s (lean-out '(log x) '(+ (* -1 x) (* x (log x))) "hyp-log")))
    (assert-true (lean-has? s "0 < x"))))

(deftest "lean: гипотеза sqrt — 0 < u"
  (let ((s (lean-out '(sqrt x) '(* 2/3 (^ x 3/2)) "hyp-sqrt")))
    (assert-true (lean-has? s "(h1 : 0 < x)"))))

(deftest "lean: гипотеза дробной степени — 0 < u"
  (let ((s (lean-out '(^ x 1/2) '(* 2/3 (^ x 3/2)) "hyp-rpow")))
    (assert-true (lean-has? s "(h1 : 0 < x)"))))

(deftest "lean: гипотеза tan — cos u ≠ 0"
  (let ((s (lean-out '(tan x) '(* -1 (log (cos x))) "hyp-tan")))
    (assert-true (lean-has? s "Real.cos (x) ≠ 0"))))

(deftest "lean: гипотеза asin — −1 < u ∧ u < 1"
  (let ((s (lean-out '(asin x) '(+ (* x (asin x)) (^ (+ 1 (* -1 (^ x 2))) 1/2)) "hyp-asin")))
    (assert-true (lean-has? s "-1 < x ∧ x < 1"))))

(deftest "lean: условие ответа становится гипотезой"
  (let ((s (lean-emit-antiderivative 'x '(* 1/2 (^ x 2)) 'x '((> x 0)) "hyp-cond")))
    (assert-true (lean-has? s "(h1 : 0 < x)"))))

(deftest "lean: непереводимое условие — unsupported, а не молчание"
  (let ((r (lean-emit-antiderivative 'x '(* 1/2 (^ x 2)) 'x '((divergent x foo)) "hyp-bad")))
    (assert-equal (car r) 'unsupported)))

(deftest "lean: в сгенерированном тексте нет sorry/admit/axiom"
  (let ((s (lean-out '(tan x) '(* -1 (log (cos x))) "no-placeholder")))
    (assert-true (not (lean-has? s "sorry")))
    (assert-true (not (lean-has? s "admit")))
    (assert-true (not (lean-has? s "axiom")))))

; ---------- П3: unsupported ----------

(deftest "lean: rootsum/erf/abs — unsupported с головой"
  (let ((r1 (lean-emit-antiderivative '(rootsum 1 2) '(rootsum 1 2) 'x '() "u1"))
        (r2 (lean-emit-antiderivative '(erf x) '(erf x) 'x '() "u2"))
        (r3 (lean-emit-antiderivative '(abs x) '(abs x) 'x '() "u3")))
    (assert-equal (car r1) 'unsupported)
    (assert-true (lean-has? (cadr r1) "rootsum"))
    (assert-equal (car r2) 'unsupported)
    (assert-true (lean-has? (cadr r2) "erf"))
    (assert-equal (car r3) 'unsupported)
    (assert-true (lean-has? (cadr r3) "abs"))))

(deftest "lean: символьный показатель степени — unsupported"
  (let ((r (lean-emit-antiderivative '(^ x a) '(^ x a) 'x '() "u4")))
    (assert-equal (car r) 'unsupported)))

; ---------- хеш и приём результатов ----------

(deftest "lean: хеш устойчив и различает тексты"
  (assert-equal (lean-hash "abc") (lean-hash "abc"))
  (assert-true (not (equal? (lean-hash "abc") (lean-hash "abd")))))

(deftest "lean: статус по хешу (passed / подделка → not-run)"
  (begin
    (lean-results-clear)
    (let* ((src (lean-out 'x '(* 1/2 (^ x 2)) "res-ok"))
           (h (lean-hash src)))
      (lean-results-add h "passed" "lean/catalog/res-ok.lean" "qedra_int_res_ok" "4.34.0-rc2" "")
      (assert-equal (cdr (assoc 'status (lean-status src))) "passed")
      (assert-equal (cdr (assoc 'status (lean-status (string-append src " ")))) "not-run")
      (lean-results-clear))))

(deftest "lean: статус failed принимается, но не выдаётся за passed"
  (begin
    (lean-results-clear)
    (let* ((src (lean-out 'x '(* 1/2 (^ x 2)) "res-bad"))
           (h (lean-hash src)))
      (lean-results-add h "failed" "lean/catalog/res-bad.lean" "qedra_int_res_bad" "4.34.0-rc2" "error: tactic 'ring' failed")
      (assert-equal (cdr (assoc 'status (lean-status src))) "failed")
      (assert-true (lean-has? (cdr (assoc 'log (lean-status src))) "ring"))
      (lean-results-clear))))

(deftest "lean: без принятых результатов сертификат generated"
  (begin
    (lean-results-clear)
    (let ((c (lean-certificate 'x '(* 1/2 (^ x 2)) 'x '())))
      (assert-equal (cdr (assoc 'status c)) "generated")
      (assert-true (string? (cdr (assoc 'source c)))))))

; ---------- L4: страж пустых теорем (пример «гипотезы совместны») ----------

(deftest "lean: страж — пример совместности есть и с точкой x = 0"
  (let ((s (lean-out '(/ 1 (sqrt (- 1 (^ x 2)))) '(asin x) "t_vac")))
    (assert-true (lean-has? s "-- vacuous-check: t_vac (x = 0)"))
    (assert-true (lean-has? s "example : ∃ x : ℝ,"))
    (assert-true (lean-has? s "refine ⟨0, "))))

(deftest "lean: страж — при гипотезе x ≠ 0 точка сдвигается с нуля"
  (let ((s (lean-out '(/ 1 x) '(log x) "t_vac2")))
    (assert-true (lean-has? s "-- vacuous-check: t_vac2 (x = 1)"))))

(deftest "lean: страж — гипотезы log попадают в пример"
  (let ((s (lean-out '(/ 1 (* x (log x))) '(log (log x)) "t_vac3")))
    (assert-true (lean-has? s "Real.log (x) ≠ 0"))))
