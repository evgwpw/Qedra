; Lisp-тесты журнала попыток, шаг D2a: explain / capture-attempts / attempts-text.
; Попытки — дерево «стратегия — успех/отказ: причина — мс»; повторы схлопываются; лимиты как у full.

; суть: тело with-step вернуло #f — в steps рамка отбрасывается, в попытках остаётся с причиной
(deftest "попытки/D2a: неудачная рамка сохраняется с причиной и статусом отказа"
  (let ((r (capture-attempts (lambda () (with-step ('test-fail "Тестовый отказ" 1) #f)))))
    ; результат — #f (значение тела)
    (assert-equal (car r) #f)
    ; дерево попыток: один узел, статус отказа, причина «нет результата (#f)»
    (let ((a (car (cadr r))))
      (assert-equal (car a) 'test-fail)
      (assert-true (string-contains? (caddr a) "отказ:"))
      (assert-true (string-contains? (caddr a) "нет результата"))
      ; время — в конце строки «— N мс»
      (assert-true (string-contains? (caddr a) "мс")))))

(deftest "попытки/D2a: успешная рамка — статус успеха и пояснение"
  (let ((r (capture-attempts (lambda () (with-step ('test-ok "Тестовый успех" 2 :comment "сработало") 7)))))
    (assert-equal (car r) 7)
    (let ((a (car (cadr r))))
      (assert-equal (car a) 'test-ok)
      (assert-true (string-contains? (caddr a) "успех:"))
      (assert-true (string-contains? (caddr a) "сработало")))))

(deftest "попытки/D2a: ошибка в теле рамки — причина из сообщения ошибки"
  ; ошибка летит наружу (рамка не глотает) — ловим try, проверяем что это ошибка car
  (let ((e (try (with-step ('test-err "Тест ошибки" 3) (car 5)) (lambda (e) e))))
    (assert-true (equal? (type-of e) 'error))))

(deftest "попытки/D2a: попытка с ошибкой фиксируется в дереве при захвате через catch"
  ; вызов ловит ошибку внутри thunk — рамка закрывается отказом с сообщением ошибки
  (let ((r (capture-attempts (lambda ()
             (try (with-step ('test-err2 "Тест ошибки 2" 10) (car 5)) (lambda (e) 'caught))))))
    (assert-equal (car r) 'caught)
    (let ((a (car (cadr r))))
      (assert-equal (car a) 'test-err2)
      (assert-true (string-contains? (caddr a) "отказ:"))
      (assert-true (string-contains? (caddr a) "car")))))

(deftest "попытки/D2a: вложенные рамки — дерево, ребёнок под родителем"
  (let ((r (capture-attempts (lambda ()
             (with-step ('outer "Внешняя" 4)
               (with-step ('inner-ok "Внутренняя успех" 5) 1)
               (with-step ('inner-fail "Внутренняя отказ" 6) #f)
               9)))))
    (assert-equal (car r) 9)
    ; дети внешней рамки: успех + отказ
    (let ((kids (nth (car (cadr r)) 6)))
      (assert-equal (length kids) 2)
      (assert-true (string-contains? (caddr (car kids)) "успех:"))
      (assert-true (string-contains? (caddr (cadr kids)) "отказ:")))))

(deftest "попытки/D2a: уровень attempts в capture-step-log не портит brief/full/trace"
  ; старые уровни работают как раньше: неудачная рамка в steps НЕ видна
  (let ((r (capture-step-log (lambda () (with-step ('test-fail2 "Отбрасывается" 7) #f)))))
    (assert-equal (cadr r) '())))

(deftest "попытки/D2a: explain печатает дерево и возвращает значение"
  ; печать идёт в stdout — проверяем только значение и отсутствие ошибки
  (assert-equal (explain-call (lambda () (with-step ('ex "Пояснение" 8 :comment "ок") 42)) 'ru) 42))

(deftest "попытки/D2a: попытки не пишутся при выключенном журнале"
  ; step-log-off: вызов без журнала не оставляет попыток
  (assert-equal (step-log-enabled?) #f)
  (let ((n (length (step-log))))
    (with-step ('no-journal "Без журнала" 9) 1)
    (assert-equal (length (step-log)) n)))

(deftest "попытки/D2a: реальные каскады — integrate даёт отказы и успехи, повторы схлопываются"
  ; интегрирование exp(x^2) не берётся: верхняя рамка — отказ; в дереве есть отказы с причиной
  (let ((r (capture-attempts (lambda () (integrate '(exp (^ x 2)) 'x)))))
    (let ((a (car (cadr r))))
      ; корень — рамка интегрирования, отказ
      (assert-true (string-contains? (caddr a) "отказ:"))
      ; попытки по Ришу тоже отказ
      (assert-true (>= (length (nth a 6)) 1)))))

(deftest "попытки/D2a: attempts-text печатает дерево (строка содержит успех/отказ и мс)"
  (let ((r (capture-attempts (lambda () (with-step ('tt "Печать" 11 :comment "пояс") 3)))))
    (let ((s (attempts-text (cadr r) #f)))
      (assert-true (string-contains? s "успех"))
      (assert-true (string-contains? s "мс"))
      (assert-true (string-contains? s "пояс")))))

(deftest "попытки/D2a: вложенный захват шагов не ломает дерево попыток"
  ; capture-step-log внутри рамки: стек попыток сохраняется и восстанавливается вместе со стеком рамок
  (let ((r (capture-attempts
             (lambda ()
               (with-step ('outer-ok "Внешняя" 1 :comment "готово")
                 (capture-step-log (lambda () (with-step ('inner "Внутренняя" 2) #f)))
                 5)))))
    (assert-equal (car r) 5)
    (let ((a (car (cadr r))))
      (assert-equal (car a) 'outer-ok)
      (assert-true (string-contains? (caddr a) "успех:")))))

; ---------- D2b: явные причины отказов стратегий ----------

; поиск узла попыток по правилу (в глубину)
(define (att-find rule nodes)
  (cond ((null? nodes) #f)
        ((equal? (car (car nodes)) rule) (car nodes))
        (else (or (att-find rule (nth (car nodes) 6))
                  (att-find rule (cdr nodes))))))

(deftest "попытки/D2b: причина отказа метода подстановки (int-usub)"
  ; foo(u) не интегрируется: рамка подстановки открылась (q2 без x) и отказала с причиной
  (let ((r (capture-attempts (lambda () (integrate '(* 2 x (foo (^ x 2))) 'x)))))
    (let ((a (att-find 'int-substitution (cadr r))))
      (assert-true a)
      (assert-true (string-contains? (caddr a) "отказ:"))
      (assert-true (string-contains? (caddr a) "через u")))))

(deftest "попытки/D2b: Риш для exp(x^2) — доказано неэлементарен, а не «нет результата»"
  (let ((r (capture-attempts (lambda () (integrate '(exp (^ x 2)) 'x)))))
    (let ((a (car (cadr r))))
      (assert-true (string-contains? (caddr a) "отказ:"))
      (assert-true (string-contains? (caddr a) "элементар")))))

(deftest "попытки/D2b: причина отказа табличной формулы (аргумент не линеен)"
  ; log(x^2): табличная строка совпала, но ?u = x^2 не линеен; интеграл берётся по частям
  (let ((r (capture-attempts (lambda () (integrate '(log (^ x 2)) 'x)))))
    (let ((a (att-find 'int-table (cadr r))))
      (assert-true a)
      (assert-true (string-contains? (caddr a) "условия табличной формулы")))))

(deftest "попытки/D2b: предел sin(x)/x — успех и отказавшая попытка с причиной"
  (let ((r (capture-attempts (lambda () (limit '(* (sin x) (^ x -1)) 'x 0)))))
    (assert-equal (car r) 1)
    (let ((root (car (cadr r))))
      (assert-true (string-contains? (caddr root) "успех:"))
      (let ((bad (filter (lambda (c) (string-contains? (caddr c) "отказ:")) (nth root 6))))
        (assert-true (>= (length bad) 1))
        (assert-true (string-contains? (caddr (car bad)) "неопределённость"))))))

(deftest "попытки/D2b: успешная стратегия не получает ложную причину отказа"
  (let ((r (capture-attempts (lambda () (integrate '(^ x 2) 'x)))))
    (let ((a (car (cadr r))))
      (assert-true (string-contains? (caddr a) "успех:"))
      (assert-equal (string-contains? (caddr a) "условия табличной формулы") #f))))
