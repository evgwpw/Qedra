; elliptic.lisp — тесты A3′.3 (часть): численные значения и производные эллиптических голов.

(deftest "a3p3: полные K(k) и E(k) — известные значения"
  (assert-true (< (abs (- (eval-num '(elliptic-k 1/2)) 1.685750354812596)) 1e-12))
  (assert-true (< (abs (- (eval-num '(elliptic-ec 1/2)) 1.4674622093394272)) 1e-12))
  ; K(0) = E(0) = π/2
  (assert-true (< (abs (- (eval-num '(elliptic-k 0)) 1.5707963267948966)) 1e-12))
  (assert-true (< (abs (- (eval-num '(elliptic-ec 0)) 1.5707963267948966)) 1e-12)))

(deftest "a3p3: неполные F, E, Π — численно и монотонно"
  (let ((f1 (eval-num '(elliptic-f 1/2 1/2)))
        (f2 (eval-num '(elliptic-f 1 1/2))))
    (assert-true (number? f1))
    (assert-true (> f2 f1)))
  (assert-true (< (abs (- (eval-num '(elliptic-e 1/2 1/2)) 0.4950017030164152)) 1e-12))
  (assert-true (number? (eval-num '(elliptic-pi 1/5 1/2 1/2)))))

(deftest "a3p3: производные по φ (d/dφ F, E, Π)"
  ; d/dφ F(φ,k) = 1/√(1−k² sin²φ)
  (let* ((d (diff 'phi '(elliptic-f phi 1/2)))
         (v (eval-num (subst '(phi 3/10) d)))
         (ref (/ 1 (sqrt (- 1 (* 1/4 (^ (sin 3/10) 2)))))))
    (assert-true (< (abs (- v (eval-num ref))) 1e-10)))
  ; d/dφ E(φ,k) = √(1−k² sin²φ)
  (let* ((d (diff 'phi '(elliptic-e phi 1/2)))
         (v (eval-num (subst '(phi 3/10) d)))
         (ref (sqrt (- 1 (* 1/4 (^ (sin 3/10) 2))))))
    (assert-true (< (abs (- v (eval-num ref))) 1e-10)))
  ; d/dφ Π(n;φ,k) = 1/((1−n sin²φ)√(1−k² sin²φ))
  (let* ((d (diff 'phi '(elliptic-pi 1/5 phi 1/2)))
         (s2 (^ (sin 3/10) 2))
         (v (eval-num (subst '(phi 3/10) d)))
         (ref (/ 1 (* (- 1 (* 1/5 s2)) (sqrt (- 1 (* 1/4 s2)))))))
    (assert-true (< (abs (- v (eval-num ref))) 1e-10))))

; ---------- A3′.3: таблица приведения к F/E ----------

(deftest "a3p3: таблица — 1/√(1−x⁴), F и E (с численной проверкой)"
  ; первый род: ответ через F, проверка квадратурой
  (let* ((e '(^ (+ 1 (* -1 (^ x 4))) -1/2))
         (a (integrate e 'x)))
    (assert-true (contains-sym? a 'elliptic-f))
    (assert-true (integrate::int-ell-check a e 'x)))
  ; F(asin x, 1/2)
  (let* ((e '(^ (* (+ 1 (* -1 (^ x 2))) (+ 1 (* -1/4 (^ x 2)))) -1/2))
         (a (integrate e 'x)))
    (assert-equal (car a) 'elliptic-f)
    (assert-true (integrate::int-ell-check a e 'x)))
  ; E(asin x, 1/2)
  (let* ((e '(* (^ (+ 1 (* -1 (^ x 2))) -1/2) (^ (+ 1 (* -1/4 (^ x 2))) 1/2)))
         (a (integrate e 'x)))
    (assert-equal (car a) 'elliptic-e)
    (assert-true (integrate::int-ell-check a e 'x))))

(deftest "a3p3: вне таблицы — честный отказ, подделка отвергается"
  ; 1/√(x⁴+2) вне таблицы (четвертая степень не сводится к 1−x⁴) — остаётся невычисленным
  (let ((a (integrate '(^ (+ 2 (^ x 4)) -1/2) 'x)))
    (assert-equal (car a) 'integrate))
  ; E вместо F для первого рода не проходит численную проверку
  (assert-equal (integrate::int-ell-check
                 '(elliptic-e (asin x) 1/2)
                 '(^ (* (+ 1 (* -1 (^ x 2))) (+ 1 (* -1/4 (^ x 2)))) -1/2)
                 'x)
                #f))

(deftest "a3p3: кубика x³+1 — комплексный модуль, производная верна"
  (let* ((e '(^ (+ 1 (^ x 3)) -1/2))
         (a (integrate e 'x)))
    (assert-true (contains-sym? a 'elliptic-f))
    ; сертификат: конечные разности ответа = 1/√(x³+1) в трёх точках
    (assert-true (integrate::int-ell-cubic-check (integrate::int-ell-cubic-answer 'x) 'x))
    ; разность значений = определённый интеграл 0..1 (квадратура 0.9096042426549512)
    (let ((v (integrate::int-ell-re (eval-num (subst '(x 1) a))))
          (v0 (integrate::int-ell-re (eval-num (subst '(x 0) a)))))
      (assert-true (number? v))
      (assert-true (< (abs (- (- v v0) 0.9096042426549512)) 1/100000)))))

; ---------- A3′.6: расширенная таблица и Π ----------

(define (a3p6-nonelementary? e)
  (let* ((r (capture-conditions (lambda () (integrate e 'x))))
         (cs (cadr r)))
    (any? (lambda (pr) (and (pair? (car pr)) (equal? (car (car pr)) 'risch-nonelementary))) cs)))

(define a3p6-rows
  (list '(* (^ x 2) (^ (- 1 (^ x 4)) -1/2))
        (list '^ '(+ 2 (* 3 (^ x 3))) -1/2)
        (list '^ '(- 1 (^ x 3)) -1/2)
        (list '^ '(* (- x 1) (- x 2) (- x 3)) -1/2)
        (list '^ '(* (+ (^ x 2) 4) (+ (^ x 2) 1)) -1/2)
        (list '^ '(* (- 4 (^ x 2)) (- 1 (^ x 2))) -1/2)))

(deftest "a3p6: новые строки таблицы — ответ через F/E/K, сертификат проходит"
  (assert-true
   (every? (lambda (e)
             (let* ((f (integrate::int-ell-form e 'x))
                    (F (integrate e 'x)))
               (and f
                    (not (integrate::int-unevaluated? F))
                    (integrate::int-ell-cert-ok? f F e 'x)
                    (or (contains-sym? F 'elliptic-f)
                        (contains-sym? F 'elliptic-e)
                        (contains-sym? F 'elliptic-k)))))
           a3p6-rows)))

(deftest "a3p6: Π третьего рода — ответ, сертификат и род"
  (let* ((e '(/ 1 (* (- 1 (* 1/2 (^ x 2))) (^ (* (- 1 (^ x 2)) (- 1 (* 1/4 (^ x 2)))) 1/2))))
         (F (integrate e 'x)))
    (assert-equal (simplify F) (simplify '(elliptic-pi 1/2 (asin x) 1/2)))
    (assert-true (integrate::int-ell-check F e 'x))
    ; третий род: nonelementary не заявляется
    (assert-true (not (a3p6-nonelementary? e))))
  ; первый род — nonelementary есть, второй (E) — нет
  (assert-true (a3p6-nonelementary? (list '^ '(* (- 4 (^ x 2)) (- 1 (^ x 2))) -1/2)))
  (assert-true (not (a3p6-nonelementary? '(* (^ (- 1 (^ x 2)) -1/2)
                                              (^ (- 1 (* 1/4 (^ x 2))) 1/2))))))

(deftest "a3p6: подделка модуля k и параметра Π ловится сертификатом"
  (let ((e (list '^ '(* (- 4 (^ x 2)) (- 1 (^ x 2))) -1/2)))
    (assert-true (integrate::int-ell-check '(* 1/2 (elliptic-f (asin x) 1/2)) e 'x))
    (assert-true (not (integrate::int-ell-check '(* 1/2 (elliptic-f (asin x) 1/3)) e 'x))))
  (let ((e '(/ 1 (* (- 1 (* 1/2 (^ x 2))) (^ (* (- 1 (^ x 2)) (- 1 (* 1/4 (^ x 2)))) 1/2)))))
    (assert-true (not (integrate::int-ell-check '(elliptic-pi 1/3 (asin x) 1/2) e 'x)))))
