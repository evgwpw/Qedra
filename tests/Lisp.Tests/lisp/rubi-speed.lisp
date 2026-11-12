; RUBI.SPEED: ускорения движка Rubi без смены семантики — индекс по классу корня образца и кэш
; чистых предикатов условий (rubi-zero?, rubi-posq/negq). Тесты проверяют, что кэш/индекс не меняют
; ответ и что кэши сбрасываются на каждый вызов rubi-integrate.
(load (string-append lib-dir "rubi/utils.lisp"))

; свой стенд (файлы тестов делят окружение — не трогаем rubi-test-setup/rubi-rule-setup)
(define (rubi-speed-setup rules)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #t)
  (for-each (lambda (r) (rubi::rubi-add-rule (car r) (cadr r) (nth r 2) (nth r 3)))
            (reverse rules))
  (rubi::rubi-build-index))

(define (rubi-speed-rule id)
  (car (filter (lambda (r) (equal? (nth r 1) id)) rubi::*rubi-rules*)))

; два верных правила: (x^2)' = x^3/3 и ∫1/(a+b x) = log(a+b x)/b. Второе записано степенью −1:
; так его образец совпадает с нормализованной формой выражения (см. тест про запись «/» ниже)
(define (rubi-speed-rules)
  (list (list "speed-pow" '(^ x 2) '() '(* 1/3 (^ (quote x) 3)))
        (list "speed-rec" '(^ (+ ?a (* ?b x)) ?n) '(rubi::rubi-eqq ?n -1)
              '(* (^ b -1) (log (+ a (* b (quote x))))))))

; --- класс корня образца (индекс правил по корню) ---

(deftest "rubi-speed: класс корня образца — голова, AC-узел, степень, переменная"
  ; классы консервативные: сомнительный случай — any (правило перебирается как раньше)
  (assert-equal (list 'head 'log 1) (rubi::rubi-pat-root-key '(log ?u)))
  (assert-equal (list 'head 'sin 1) (rubi::rubi-pat-root-key '(sin (* 2 ?u))))
  (assert-equal 'pair (rubi::rubi-pat-root-key '(?f ?u)))
  (assert-equal (list 'ac '*) (rubi::rubi-pat-root-key '(* 2 (^ x 3))))
  ; степень: правило (^ ?u ?n) подходит и выражению-не-степени (единица степени), поэтому any
  (assert-equal 'any (rubi::rubi-pat-root-key '(^ ?u ?n)))
  ; AC-узел с переменной-аргументом: переменная может получить нейтральный элемент — any
  (assert-equal 'any (rubi::rubi-pat-root-key '(* ?a ?b x)))
  (assert-equal 'any (rubi::rubi-pat-root-key '?u)))

(deftest "rubi-speed: класс корня считается по нормализованному образцу (запись / в правиле)"
  ; было: класс брался из исходного образца, правило (/ 1 (+ a b x)) получало (head / 2) и отсеивалось
  ; навсегда — выражение к тому времени уже (* ... (^ ... -1)). Так терялись 64 задачи ok-sample.
  (let* ((pat (ac-strip-units (ac-norm '(/ 1 (+ a (* b x))))))
         (k (rubi::rubi-pat-root-key pat)))
    ; 1/X нормализуется в X^(-1) — корень-степень, класс any (не «голова /»)
    (assert-equal k 'any)
    (assert-true (rubi::rubi-root-ok? k '(^ (+ a (* b x)) -1))))
  ; у правила из rubi-add-rule то же: класс берётся из того же выражения, «головы /» в классе нет
  (rubi-speed-setup (list (list "speed-frac" '(/ ?c (+ a (* b x))) '() '(* ?c (log (+ a (* b (quote x))))))))
  (assert-equal (rubi::rubi-rule-root-key (rubi-speed-rule "speed-frac")) 'any))

(deftest "rubi-speed: индекс по корню не отсекает правило, которое подходит"
  (rubi-speed-setup (rubi-speed-rules))
  (assert-equal (simplify (rubi-integrate '(/ 1 (+ a (* b x))) 'x))
                (simplify '(* (^ b -1) (log (+ a (* b x))))))
  (assert-equal (simplify (rubi-integrate '(^ x 2) 'x))
                (simplify '(* 1/3 (^ x 3)))))

(deftest "rubi-speed: ответ не зависит от фильтра по корню"
  (rubi-speed-setup (rubi-speed-rules))
  (let ((on (rubi-integrate '(/ 1 (+ a (* b x))) 'x)))
    (unwind-protect
     (begin (set! rubi::*rubi-root-filter* #f)
            (assert-equal on (rubi-integrate '(/ 1 (+ a (* b x))) 'x)))
     (set! rubi::*rubi-root-filter* #t))))

; --- проверка ответа движка Rubi без лишнего together (шаг RUBI.SPEED.3, lib/integrate/check.lisp) ---

(deftest "rubi-speed: int-check-rubi — подделка отвергается"
  ; производная x^2 не равна x^2; 2√(1+x²) — не первообразная √(1+x²)
  (assert-equal #f (int-check-rubi '(^ x 2) '(^ x 2) 'x))
  (assert-equal #f (int-check-rubi '(* 2 (^ (+ 1 (^ x 2)) 1/2)) '(^ (+ 1 (^ x 2)) 1/2) 'x))
  (assert-equal 'bad (int-check-rubi-how '(* 2 (^ (+ 1 (^ x 2)) 1/2)) '(^ (+ 1 (^ x 2)) 1/2) 'x)))

(deftest "rubi-speed: int-check-rubi — верный ответ с ветвлением принимается численно, без together"
  ; ∫√(1−x²) = (x√(1−x²) + asin x)/2: simplify не доказывает (главные значения √(x⁻²)), доказывает сверка в точках
  (let ((f '(* 1/2 (+ (* x (^ (- 1 (^ x 2)) 1/2)) (asin x)))) (e '(^ (- 1 (^ x 2)) 1/2)))
    (assert-equal 'numeric (int-check-rubi-how f e 'x))
    (assert-equal #t (int-check-rubi f e 'x))
    ; каскад integrate не тронут: int-check/int-check-how остаются прежними
    (assert-equal #t (int-check f e 'x))
    (assert-equal 'numeric (int-check-how f e 'x))))

(deftest "rubi-speed: int-check-rubi — точное доказательство simplify остаётся первым"
  (assert-equal 'simplify (int-check-rubi-how '(^ (+ 1 (^ x 2)) 3/2) '(* 3 x (^ (+ 1 (^ x 2)) 1/2)) 'x))
  (assert-equal #t (int-check-rubi '(^ (+ 1 (^ x 2)) 3/2) '(* 3 x (^ (+ 1 (^ x 2)) 1/2)) 'x)))

; --- кэш чистых предикатов условий (rubi-zero?, rubi-posq/negq) ---

(deftest "rubi-speed: кэш rubi-zero? не меняет ответ"
  (rubi-speed-setup (rubi-speed-rules))
  (let ((e '(- (^ x 2) (* x x))))
    (assert-equal #t (rubi::rubi-zero? e))
    (assert-equal #t (rubi::rubi-zero? e))     ; второй раз — из кэша
    (assert-equal #f (rubi::rubi-zero? '(- (^ x 2) 1)))
    (assert-equal #f (rubi::rubi-zero? '(- (^ x 2) 1))))
  ; число мимо кэша, составное выражение — в кэш
  (assert-true (> (length (hash-keys rubi::*rubi-zero-cache*)) 0)))

(deftest "rubi-speed: кэш rubi-posq/negq согласован с самим предикатом"
  (rubi-speed-setup (rubi-speed-rules))
  (let ((e '(- (^ 2 1/2) 1)))
    (assert-equal #t (rubi::rubi-posq e))
    (assert-equal #t (rubi::rubi-posq e))
    (assert-equal #f (rubi::rubi-negq e))
    (assert-equal #f (rubi::rubi-posq (list '- 1 (list '^ 2 1/2))))))

(deftest "rubi-speed: кэши предикатов и кандидатов сбрасываются между вызовами"
  ; Кэши живут один вызов rubi-integrate: значения зависят только от аргумента, но копить их между
  ; задачами нельзя (кэш кандидатов ещё и от формы выражения) — проверяем, что хеши создаются заново.
  (rubi-speed-setup (rubi-speed-rules))
  (let ((z0 rubi::*rubi-zero-cache*) (p0 rubi::*rubi-posq-cache*) (c0 rubi::*rubi-cands2*))
    (rubi::rubi-zero? '(- (^ x 2) (* x x)))
    (rubi-integrate '(^ x 2) 'x)
    (assert-true (not (equal? z0 rubi::*rubi-zero-cache*)))
    (assert-true (not (equal? p0 rubi::*rubi-posq-cache*)))
    (assert-true (not (equal? c0 rubi::*rubi-cands2*)))))

(deftest "rubi-speed: кэш кандидатов на выражение хранит список, форму и степени"
  (rubi-speed-setup (rubi-speed-rules))
  (rubi-integrate '(/ 1 (+ a (* b x))) 'x)
  (let ((vals (map (lambda (k) (hash-ref rubi::*rubi-cands2* k)) (hash-keys rubi::*rubi-cands2*))))
    (assert-true (> (length vals) 0))
    (for-each (lambda (v) (assert-true (= (length v) 3))) vals)))
