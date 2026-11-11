; LEAN.L1/L2: генератор .lean — эталоны (10 файлов каталога), гипотезы, unsupported, хеш, приём результатов.

(define (lean-file id) (read-text-file (string-append "lean/catalog/" id ".lean")))
(define (lean-check f F id)
  (let ((r (lean-emit-antiderivative f F 'x '() id)))
    (assert-true (string? r))
    (assert-equal r (lean-file id))))
(define (lean-out f F id) (lean-emit-antiderivative f F 'x '() id))
(define (lean-has? s part) (string-contains? s part))

; ---------- П1: 10 эталонов (текст сверяется с lean/catalog/<id>.lean) ----------

(deftest "lean: эталон x → x^2/2" (lean-check 'x '(* 1/2 (^ x 2)) "int_0001"))
(deftest "lean: эталон 1/x → log x" (lean-check '(/ 1 x) '(log x) "int_0004"))
(deftest "lean: эталон x*exp(x^2) → exp(x^2)/2" (lean-check '(* x (exp (^ x 2))) '(* 1/2 (exp (^ x 2))) "int_0006"))
(deftest "lean: эталон sin x → −cos x" (lean-check '(sin x) '(* -1 (cos x)) "int_0010"))
(deftest "lean: эталон tan x → −log(cos x)" (lean-check '(tan x) '(* -1 (log (cos x))) "int_0012"))
(deftest "lean: эталон sqrt x → 2/3 x^(3/2)" (lean-check '(sqrt x) '(* 2/3 (^ x 3/2)) "int_0014"))
(deftest "lean: эталон x^2*sin x" (lean-check '(* (^ x 2) (sin x)) '(+ (* -1 (^ x 2) (cos x)) (* 2 (+ (* x (sin x)) (cos x)))) "int_0018"))
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
