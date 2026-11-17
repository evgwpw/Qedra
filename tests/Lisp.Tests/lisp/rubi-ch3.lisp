; RUBI.CH3: глава 3 (логарифмы) — выборка отказов `research/rubi/ch3-unknown-500.tsv` (журнал diagnose-run, бюджет 6 с):
; до правок ok 2 из 500 (check 238, rhs-no-rule 174, бюджет 86). Найдены дефекты, общие для нескольких глав:
;   1. PolyLog в правых частях генерировался как голова `polylog`, которой нет в диалекте (ошибка «Неизвестный символ»):
;      правила 3.1.5, 3.2.3, 3.3, 3.4, 3.5, 5.3.x, 7.3.x, 8.8 (273 места) — внесено RUBI.CH8 (`rubi::rubi-polylog`, при переносе на master оставлена его обёртка).
;   2. Dist[u, v, x] (3 аргумента) — ошибка арности в 3.1.3 #18 и 3.5 #37/#38.
;   3. E в правой части был (exp 1) = плавающее 2.718…, из-за чего подзадача (^ 2.718 …) не сопоставлялась с правилами
;      2.x; теперь символ E (проверка ответа возвращает E к exp), а показатель F^(c d x) группируется как g_.*(e_.+f_.*x_).
;   4. Условия, записанные численной проверкой кандидата (2F1 при z = 1), не попадают в канал условий ответа.
;   5. (RUBI.CH3.2) унарный минус разбирался сильнее степени: Mathematica `-F^x` = -(F^x), а генератор давал (-F)^x —
;      432 правила в 117 файлах (в том числе 2.1 #6, 1.1.2.x, 1.1.3.x); исправлены `tools/rubi/mma.mjs` и тела правил.

(load (string-append lib-dir "rubi/utils.lisp"))

(deftest "rubi-ch3/1: PolyLog — ∫ log(1+e x)/x = -Li2(-e x) (3.3 #3)"
  (rubi-integrate 1 'x)   ; загрузка правил не входит в бюджет вызова
  (let ((r (rubi-integrate (math-read "log(1 + e*x)/x") 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (contains-sym? r 'polylog))
    (assert-equal '(* -1 (polylog 2 (* -1 e x))) r)))

(deftest "rubi-ch3/2: rubi-polylog — голова polylog; Dist принимает 2 и 3 аргумента"
  (assert-equal '(polylog 2 x) (rubi::rubi-polylog 2 'x))
  (assert-equal (rubi::rubi-dist 2 '(+ x 1)) (rubi::rubi-dist 2 '(+ x 1) 'x))
  (assert-equal (simplify '(+ (* 2 x) 2)) (simplify (rubi::rubi-dist 2 '(+ x 1) 'x))))

(deftest "rubi-ch3/3: E правой части — символ, а не 2.718…; ∫ exp(x²) = erfi (2.3), ∫ exp(x)/x = Ei"
  (assert-equal 'E (rubi::rubi-num-exp 1))
  (assert-equal '(^ E 2) (rubi::rubi-num-exp 2))
  (assert-equal '(* 1/2 (^ pi 1/2) (erfi x)) (rubi-integrate (math-read "exp(x^2)") 'x)))

(deftest "rubi-ch3/5: унарный минус слабее степени (RUBI.CH3.2) — 2.1 #6 = -F^(…)·Γ(m+1, …), а не (-F)^(…)"
  ; генератор (tools/rubi/mma.mjs) разбирал -F^x как (-F)^x: 432 правила в 117 файлах (2.1 #6, 1.1.2.x, 1.1.3.x, 5.3.x, 7.3.x…)
  (assert-true (not (string-contains? (read-text-file (string-append lib-dir "rubi/rules/2.1.body.lisp")) "(^ (- F) (* g")))
  (let ((r (rubi-integrate (math-read "exp(x)*(a + b*x)^p") 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (contains-sym? r 'gamma))
    ; ответ верный: d/dx = подынтегральное (численно в точке при заданных a, b, p)
    (let* ((vals '((a 1/2) (b 3) (p 3/2) (x 7/10)))
           (rv (lambda (e) (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr))) e vals))))
      (assert-true (< (abs (- (eval-num (rv (diff 'x r)))
                              (eval-num (rv '(* (exp x) (^ (+ a (* b x)) p))))))
                      1e-9)))))

(deftest "rubi-ch3/6: x^m (a+b log(c x^n))^p через Γ (3.1.2 #10 -> 2.1 #6)"
  (let ((r (rubi-integrate (math-read "x^(-5)*(a + b*log(c*x^n))^p") 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (contains-sym? r 'gamma))))

(deftest "rubi-ch3/7: проверка кандидата не пишет условия в канал ответа (2F1 при z = 1)"
  (conditions-clear)
  (let ((r (integrate '(/ 1 (log x)) 'x)))
    (assert-equal '(li x) r)
    (assert-equal '() (conditions))))
