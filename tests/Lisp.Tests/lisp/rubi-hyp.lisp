; RUBI.HYP: гиперболические функции (глава 6) — сведение к тригонометрии мнимого аргумента.
; Источник семантики — Rubi 4.17.3.0 (commit 61e9c18, tools/rubi/src/IntegrationUtilityFunctions.m):
;   DeactivateTrigAux 6198-6219 (гиперболические клаузы 6210-6218),
;   UnifyInertTrigFunction 6549-7362 (в порте — ядро), ReduceInertTrig 6496-6539;
;   обратный переход (I*sin -> sinh и т. п.) в исходнике делает Simplify Математики на ответе.
(load (string-append lib-dir "rubi/utils.lisp"))
(load (string-append lib-dir "rubi/engine.lisp"))

; другие файлы тестов подменяют правила Rubi игрушечными наборами - возвращаем настоящие
(define (rhyp-fresh)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #f)
  (set! rubi::*rubi-stage* 0)
  (set! rubi::*rubi-bodies* (make-hash))
  (set! rubi::*rubi-bodies-loaded* (make-hash)))

; Сравнение по значению: порядок множителей/слагаемых после ac-norm и simplify не фиксирован
; (зависит от состояния сопоставителя), поэтому структуру не сверяем — только разность.
(define (rhyp-same? a b) (equal? 0 (simplify (list '- a b))))
(define (assert-same actual expected)
  (if (rhyp-same? actual expected)
      #t
      (error (string-append "assert-same: получено " (to-string actual) " [" (math-print actual)
                            "], ожидалось " (to-string expected) " [" (math-print expected) "]"))))

; --- 1) DeactivateTrigAux: гиперболическая голова линейного аргумента (IUF.m:6210-6218) ---

(deftest "rubi-hyp/1: DeactivateTrigAux — шесть голов, все клаузы 6213-6218"
  ; sinh z -> -I sin[I z], cosh z -> cos[I z], tanh z -> -I tan[I z],
  ; coth z -> I cot[I z], sech z -> sec[I z], csch z -> I csc[I z]
  (assert-same (rubi::rubi-deactivate-trig-aux '(sinh x) 'x) '(* -1 %i (sin (* %i x))))
  (assert-same (rubi::rubi-deactivate-trig-aux '(cosh x) 'x) '(cos (* %i x)))
  (assert-same (rubi::rubi-deactivate-trig-aux '(tanh x) 'x) '(* -1 %i (tan (* %i x))))
  (assert-same (rubi::rubi-deactivate-trig-aux '(coth x) 'x) '(* %i (cot (* %i x))))
  (assert-same (rubi::rubi-deactivate-trig-aux '(sech x) 'x) '(sec (* %i x)))
  (assert-same (rubi::rubi-deactivate-trig-aux '(csch x) 'x) '(* %i (csc (* %i x)))))

(deftest "rubi-hyp/1: DeactivateTrigAux — линейный аргумент a+b*x, v = ExpandToSum[I*z] (6211)"
  ; expand распределяет I по сумме, как ExpandToSum в исходнике
  (assert-same (rubi::rubi-deactivate-trig-aux '(sinh (+ a (* b x))) 'x)
                '(* -1 %i (sin (+ (* %i a) (* %i b x)))))
  (assert-true (rubi::rubi-has-head? (rubi::rubi-deactivate-trig-aux '(cosh (+ c (* d x))) 'x) 'cos)))

(deftest "rubi-hyp/1: DeactivateTrigAux — подделки: нелинейный аргумент и обычная тригонометрия"
  ; LinearQ[u[[1]],x] ложно для x^2 — гиперболическая клауза не применяется (6210)
  (assert-same (rubi::rubi-deactivate-trig-aux '(sinh (^ x 2)) 'x) '(sinh (^ x 2)))
  ; тригонометрическая клауза 6201 к гиперболическим головам не применяется (иначе подмена на sec/csc)
  (assert-true (not (rubi::rubi-has-head? (rubi::rubi-deactivate-trig-aux '(tanh a) 'x) 'sec)))
  ; обычная тригонометрия идёт прежним путём: фаза Pi у tan снимается
  (assert-same (rubi::rubi-deactivate-trig-aux '(sin (+ a (* b x))) 'x) '(sin (+ a (* b x))))
  (assert-same (rubi::rubi-deactivate-trig-aux '(tan (+ pi (* 2 x))) 'x) '(tan (* 2 x))))


; --- 2) rubi-simplify-inert: гиперболические входы (точка нормализации, engine.lisp) ---

(deftest "rubi-hyp/2: rubi-simplify-inert сводит гиперболические, мнимый аргумент не унифицируется"
  (assert-same (rubi::rubi-simplify-inert '(sinh x) 'x) '(* -1 %i (sin (* %i x))))
  (assert-same (rubi::rubi-simplify-inert '(cosh x) 'x) '(cos (* %i x)))
  ; cos[I z] -> sin[I z + Pi/2] (IUF.m:6588-6590) сломало бы обратный переход: унификация пропускается
  (assert-same (rubi::rubi-simplify-inert '(cosh (* 2 x)) 'x) '(cos (* %i (* 2 x))))
  ; степень гиперболической: рекурсия DeactivateTrigAux по узлам (6219)
  (assert-same (rubi::rubi-simplify-inert '(^ (sinh x) 2) 'x) '(^ (* -1 %i (sin (* %i x))) 2))
  ; подделка: обычная тригонометрия не изменилась
  (assert-same (rubi::rubi-simplify-inert '(^ (cos x) 3) 'x) '(^ (sin (+ x (/ pi 2))) 3)))

; --- 3) rubi-imag-arg / rubi-hyp-from-imag: обратный переход ---

(deftest "rubi-hyp/3: rubi-imag-arg — z из I*z, в том числе по слагаемым и во вложенном произведении"
  (assert-same (rubi::rubi-imag-arg '(* %i x)) 'x)
  (assert-same (rubi::rubi-imag-arg '%i) 1)
  ; коэффициент-произведение после rubi-group-free: (* (* %i b) x)
  (assert-same (rubi::rubi-imag-arg '(* (* %i b) x)) '(* b x))
  ; сумма слагаемых I*z_k сводится в I*(сумма z_k), как ExpandToSum[I*u,x]
  (assert-same (rubi::rubi-imag-arg '(+ (* %i a) (* (* %i b) x))) '(+ a (* b x)))
  ; подделки: вещественный аргумент, I^2 = -1 (вещественное), два I подряд
  (assert-true (not (rubi::rubi-imag-arg '(+ a (* b x)))))
  (assert-true (not (rubi::rubi-imag-arg '(* (^ %i 2) x))))
  (assert-true (not (rubi::rubi-imag-arg '(* %i %i x))))
  ; I^3 = -I, поэтому z = -x (знак уходит в аргумент, как в ExpandToSum)
  (assert-same (rubi::rubi-imag-arg '(* (^ %i 3) x)) '(* -1 x)))

(deftest "rubi-hyp/3: rubi-hyp-from-imag — шесть голов и степени"
  (assert-same (rubi::rubi-hyp-from-imag '(sin (* %i x))) '(* %i (sinh x)))
  (assert-same (rubi::rubi-hyp-from-imag '(cos (* %i x))) '(cosh x))
  (assert-same (rubi::rubi-hyp-from-imag '(tan (* %i x))) '(* %i (tanh x)))
  (assert-same (rubi::rubi-hyp-from-imag '(cot (* %i x))) '(* -1 %i (coth x)))
  (assert-same (rubi::rubi-hyp-from-imag '(sec (* %i x))) '(sech x))
  (assert-same (rubi::rubi-hyp-from-imag '(csc (* %i x))) '(* -1 %i (csch x)))
  (assert-same (rubi::rubi-hyp-from-imag '(cos (+ (* %i a) (* (* %i b) x)))) '(cosh (+ a (* b x))))
  (assert-same (rubi::rubi-hyp-from-imag '(^ (cos (* %i x)) 2)) '(^ (cosh x) 2)))

(deftest "rubi-hyp/3: rubi-hyp-from-imag — подделки: вещественный аргумент и не тригонометрия"
  (assert-same (rubi::rubi-hyp-from-imag '(sin (+ a (* b x)))) '(sin (+ a (* b x))))
  (assert-same (rubi::rubi-hyp-from-imag '(sinh x)) '(sinh x))
  (assert-same (rubi::rubi-hyp-from-imag '(* 2 (cos (* %i x)))) '(* 2 (cosh x)))
  ; смешанный аргумент (не чисто мнимый) не переписывается: sin(1 + I x) не гиперболическая функция
  (assert-same (rubi::rubi-hyp-from-imag '(sin (+ 1 (* %i x)))) '(sin (+ 1 (* %i x)))))

; --- 4) Движок: ответы на гиперболических входах ---

(deftest "rubi-hyp/4: ∫sinh x = cosh x, ∫cosh x = sinh x"
  (rhyp-fresh)
  (assert-equal (rubi-integrate '(sinh x) 'x) '(cosh x))
  (assert-equal (rubi-integrate '(cosh x) 'x) '(sinh x)))

(deftest "rubi-hyp/4: ∫sinh(a+b x) и ∫cosh(a+b x) — гиперболическая форма без %i, производная верна"
  (rhyp-fresh)
  (let* ((e1 (math-read "sinh(a + b*x)"))
         (e2 (math-read "cosh(a + b*x)"))
         (r1 (rubi-integrate e1 'x))
         (r2 (rubi-integrate e2 'x)))
    (assert-true (rubi::rubi-has-head? r1 'cosh))
    (assert-true (rubi::rubi-has-head? r2 'sinh))
    ; обратный переход: в ответе не осталось %i
    (assert-true (not (contains-sym? r1 '%i)))
    (assert-true (not (contains-sym? r2 '%i)))
    (assert-true (rubi::rubi-int-check r1 e1 'x))
    (assert-true (rubi::rubi-int-check r2 e2 'x))
    ; подделка против int-check: гиперболический ответ без множителя 1/b отвергается
    (assert-true (not (rubi::rubi-int-check (list 'cosh (cadr e1)) e1 'x)))))


(deftest "rubi-hyp/3: rubi-hyp-from-imag — подделки: вещественный аргумент и не тригонометрия"
  (assert-equal '(sin (+ a (* b x))) (rubi::rubi-hyp-from-imag '(sin (+ a (* b x)))))
  (assert-equal '(sinh x) (rubi::rubi-hyp-from-imag '(sinh x)))
  (assert-equal '(* 2 (cosh x)) (rubi::rubi-hyp-from-imag '(* 2 (cos (* %i x)))))
  ; смешанный аргумент (не чисто мнимый) не переписывается: sin(1 + I x) не гиперболическая функция
  (assert-equal '(sin (+ 1 (* %i x))) (rubi::rubi-hyp-from-imag '(sin (+ 1 (* %i x))))))
