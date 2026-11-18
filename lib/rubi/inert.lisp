; rubi/inert.lisp — RUBI.NF.2: инертная тригонометрия по исходнику Rubi.
;
; В Mathematica инертные головы (sin..csc строчными) — отдельные символы от Sin..Csc: DeactivateTrig
; переводит выражение в инертную форму, правила главы 4 написаны через неё, ActivateTrig возвращает
; обратно (IUF.m:6180 — подстановка шести имён). В порте головы правил уже строчные (генератор переводит
; Sin -> sin), поэтому инертная и активная формы здесь — ОДНА И ТА ЖЕ: ActivateTrig/DeactivateTrig не
; переименовывают символы, а дают нормализацию инертной тригонометрии (Aux -> Fix -> Unify, IUF.m:6195).
;
; Клаузы FixInertTrigFunction (IUF.m:6228-6484, 57 шт.) и UnifyInertTrigFunction (IUF.m:6549-7362, 75 шт.)
; не написаны руками, а СГЕНЕРИРОВАНЫ tools/rubi/inert.mjs в lib/rubi/inert-rules.lisp — по записи на
; клаузу с номером строки источника. Применение — ac-match + вычисление условия, в порядке источника;
; рекурсия клауз идёт через сами правые части (они зовут rubi-fix-inert-trig-function) и терминальна,
; потому что последняя клауза таблицы возвращает выражение без изменений (6484 / 7294).
; Четыре клаузы с образцом-головой-переменной (f_[v_], 6466-6479) не портированы: сопоставитель порта
; не связывает головы — они помечены в таблице как unsupported.
(module rubi)

(define *rubi-inert-tables* (make-hash))
; Выключатель: #t — сгенерированная таблица клауз, #f — ручной порт (utils.lisp). Включено с MATCH.ONE:
; сопоставитель умеет вырожденные узлы + и * (OneIdentity, как в Mathematica), поэтому клаузы
; (a_.+b_.*cos[e_.+f_.*x_])^n_. совпадают и с голым cos[x]^n. Значение #f оставлено как запасной путь:
; с ним работает ручной порт клауз, и любой дефект таблицы можно изолировать.
(define *rubi-inert-generated* #t)
; Действует ли таблица СЕЙЧАС. Клаузы исходника написаны на языке инертных голов (sec/csc/cot как есть) —
; это форма автовычисления Mathematica, т.е. *rubi-nf* (шаг 1). В старой форме порта (*rubi-nf* #f)
; упрощатель и ac-norm сводят sec -> 1/cos, csc -> 1/sin, и к такой записи клаузы не применимы (проверено:
; с включённой таблицей в старой форме падают rubi-ch4/10,11,13, rubi-c ×3, rubi-hyp/2 — все «другая
; форма, равная по значению», — и теряются ответы rubi-ch4/6, rubi-backtrack/2). Там работает ручной
; порт клауз (utils.lisp), написанный под эту форму; таблица включается вместе с единой формой.
(define (rubi-inert-generated-active?) (and *rubi-inert-generated* *rubi-nf*))

; регистрация таблицы из lib/rubi/inert-rules.lisp (вызывается при загрузке файла)
(define (rubi-inert-clauses name entries) (hash-set! *rubi-inert-tables* name entries))

; доступ к таблице и переключатель для тестов: set! на переменную модуля снаружи не действует
; (та же причина, что у ac-trig-recip!)
(define (rubi-inert-table name) (hash-ref *rubi-inert-tables* name))
(define (rubi-inert-generated! v) (set! *rubi-inert-generated* v) v)

; --- вспомогательные предикаты клауз ---
(define (rubi-integersq &rest xs) (every? integer? xs))

; PowerOfInertTrigSumQ[u,func,x] — IUF.m:6487: u — степень суммы, в которой func встречается
; только как (c*func[w])^n: (a+b*(c*f[w])^n)^p либо (a+b*(d*f[w])^p+c*(d*f[w])^q)^n.
(define (rubi-inert-func-power? e func x)
  ; (c*func[w])^n или func[w]^n или func[w] — с c,n, свободными от x
  (cond ((not (pair? e)) (and (null? e) #f))
        ((equal? (car e) '^)
         (and (= (length e) 3) (rubi-power-of-func? (cadr e) func x) (rubi-freeq (caddr e) x)))
        (else (rubi-power-of-func? e func x))))
(define (rubi-power-of-func? e func x)
  (cond ((not (pair? e)) #f)
        ((equal? (car e) func)
         (and (= (length e) 2) (rubi-freeq (cadr e) x)))
        ((and (equal? (car e) '*) (= (length e) 3) (rubi-freeq (cadr e) x))
         (rubi-power-of-func? (caddr e) func x))
        (else #f)))
(define (rubi-inert-terms u)
  (if (and (pair? u) (equal? (car u) '+)) (map rubi-inert-split-term (cdr u)) (list (cons 1 u))))
; (коэффициент . основа) для слагаемого a_.*t_ (+ необязательный числовой множитель)
(define (rubi-inert-split-term t)
  (cond ((and (pair? t) (equal? (car t) '*) (= (length t) 3) (number? (cadr t))) (cons (cadr t) (caddr t)))
        ((and (pair? t) (equal? (car t) '*) (> (length t) 2)
              (every? (lambda (f) (or (number? f) (rubi-freeq f 'x))) (cdr t)))
         (cons 0 t))
        ((rubi-freeq t 'x) (cons 0 t))
        (else (cons 1 t))))
(define (rubi-power-of-inert-trig-sumq u func x)
  (if (not (and (pair? u) (equal? (car u) '^) (= (length u) 3))) #f
      (let* ((base (cadr u)) (p (caddr u))
             (ts (rubi-inert-terms base))
             (var (filter (lambda (pr) (not (rubi-freeq (cdr pr) x))) ts))
             (con (filter (lambda (pr) (rubi-freeq (cdr pr) x)) ts)))
        (cond ((not (rubi-freeq p x)) #f)
              ; (a+b*(c*f[w])^n)^p: ровно одно x-слагаемое, оно степень func
              ((and (= (length var) 1) (null? (cdr var)) (rubi-inert-func-power? (cdr (car var)) func x))
               (let ((a (if (null? con) 0 (cdr (car con)))))
                 (not (and (rubi-eqq a 0)
                           (or (rubi-integerq p)
                               (and (pair? (cdr (car var))) (equal? (car (cdr (car var))) '^)
                                    (rubi-eqq (caddr (cdr (car var))) 1)))))))
              ; (a+b*(d*f[w])^p+c*(d*f[w])^q)^n: два x-слагаемых с одной головой
              ((and (= (length var) 2) (every? (lambda (pr) (rubi-inert-func-power? (cdr pr) func x)) var)) #t)
              (else #f)))))


; --- применение таблицы ---
; Образцы клауз скомпилированы один раз (ac-build-prepared) и сопоставляются в явном режиме разметки
; (как правила Rubi: ac-match-prepared), с точной семантикой OneIdentity (:one-identity #t, MATCH.ONE):
; узел + или * из одного аргумента выражения может взять одна переменная образца, остальные обязаны быть
; необязательными (?x.). Без этого клаузы вида (a_.+b_.*cos[e_.+f_.*x_])^n_. не совпадают с голым cos[x]^n,
; а клауза (* ?a ?u) (IUF.m:6228) совпадала бы со всем подряд и уводила правую часть в рекурсию саму в себя.
(define *rubi-inert-prep* (make-hash))
(define (rubi-inert-prepared pat)
  (or (hash-ref *rubi-inert-prep* pat)
      (let ((p (ac-build-prepared pat)))
        (hash-set! *rubi-inert-prep* pat p)
        p)))
(define (rubi-inert-norm u) (ac-strip-units (ac-norm u)))

; bindings ac-match: (?имя значение). В сгенерированных клаузах правые части и условия написаны
; именами без знака вопроса (как в IUF.m), поэтому переменные let — имя без ведущего ? и без точки
; (точка в образце — признак необязательности, ?a.).
(define (rubi-inert-var name)
  (let* ((s (to-string name)) (n (string-length s))
         (s (if (and (> n 0) (equal? (substring s 0 1) "?")) (substring s 1 n) s))
         (n (string-length s)))
    (string->symbol (if (and (> n 1) (equal? (substring s (- n 1) n) ".")) (substring s 0 (- n 1)) s))))

(define (rubi-inert-eval binds x expr)
  ; привязка имени x (переменная образца ?x) не должна затенять переменную интегрирования x:
  ; в IUF.m образец пишется как (a_.+b_.*Cos[e_.+f_.*x_])^n_. с параметром x_ — в Mathematica это ОДНО
  ; имя, т.е. ?x обязана совпасть с x интегрирования (см. rubi-inert-x-ok?); в правой части и условии
  ; x — переменная интегрирования.
  (eval (list 'let (cons (list 'x (list 'quote x))
                         (cons (list 'pi (list 'quote 'pi))
                               (map (lambda (b) (list (rubi-inert-var (car b)) (list 'quote (cadr b))))
                                    (filter (lambda (b) (not (equal? (rubi-inert-var (car b)) 'x))) binds))))
              expr)))

(define rubi-inert-depth 0)
(define rubi-inert-depth-max 48)

; ?x в клаузах IUF.m — то же имя, что параметр x_ функции (Mathematica: повторная именованная образец-
; переменная требует равенства). Значит клауза применима, только если её ?x связалась с x интегрирования;
; иначе (cos y) дал бы sin(x+Pi/2) вместо sin(y+Pi/2).
(define (rubi-inert-x-ok? binds x)
  (let ((b (assoc '?x binds)))
    (or (not b) (equal? (cadr b) x))))

; Привязки, при которых условие клаузы истинно. Mathematica при ложном Condition продолжает перебор
; решений образца (Flat/Orderless даёт их несколько: (cos x) против (* ?f. ?x) даёт и (?f x, ?x 1),
; и (?f 1, ?x x)), а порт раньше брал ПЕРВОЕ решение ac-match и при ложном условии отбрасывал клаузу
; целиком — из-за этого Unify не переводил cos[v] в sin[v+Pi/2] (IUF.m:6588): условие FreeQ[{a,b,e,f,n},x]
; на первом решении ложно. Теперь: первое решение проверяется сразу (быстрый путь), при неудаче —
; перебор всех решений по порядку (ac-match-all) до первого, где условие истинно.
(define (rubi-inert-cond-ok? binds x cond)
  (car (capture-conditions (lambda () (not (equal? (rubi-inert-eval binds x cond) #f))))))

(define (rubi-inert-first-binds prep ne x cond)
  (let ((b (ac-match-prepared prep ne #f #t)))
    (cond ((not b) #f)
          ((and (rubi-inert-x-ok? b x) (rubi-inert-cond-ok? b x cond)) b)
          (else
           ; перебор всех решений: с ac-id-skip необязательная переменная может остаться без аргумента
           ; не только в хвосте, поэтому один элемент попадает в разные переменные образца
           ; (Mathematica перебирает и так: (* ?f. ?x) против x даёт и (?f x, ?x 1), и (?f 1, ?x x))
           (let ((old match::ac-id-skip))
             (set! match::ac-id-skip #t)
             (let* ((all (try (ac-match-prepared prep ne #f #t #t) (lambda (e) #f)))
                    (hit (let loop ((bs all))
                           (cond ((not (pair? bs)) #f)
                                 ((and (rubi-inert-x-ok? (car bs) x) (rubi-inert-cond-ok? (car bs) x cond))
                                  (car bs))
                                 (else (loop (cdr bs)))))))
               (set! match::ac-id-skip old)
               hit))))))

; Применяет первую подходящую клаузу таблицы (порядок — как в IUF.m). Это переписывание ОДНОГО узла:
; рекурсию по подвыражениям делают сами правые части (они зовут rubi-fix-inert-trig-function).
(define (rubi-inert-apply table u x)
  (let ((entries (hash-ref *rubi-inert-tables* table)))
    (if (or (null? entries) (> rubi-inert-depth rubi-inert-depth-max))
        u
        (let loop ((es entries))
          (cond ((null? es) u)
                ((equal? (car (car es)) 'unsupported) (loop (cdr es)))
                (else
                 (let* ((e (car es))
                        (binds (rubi-inert-first-binds (rubi-inert-prepared (nth e 1))
                                                       (rubi-inert-norm u) x (nth e 2))))
                   (if binds
                       (let ((r (try (car (capture-conditions
                                           (lambda ()
                                             (set! rubi-inert-depth (+ rubi-inert-depth 1))
                                             (rubi-inert-eval binds x (nth e 3)))))
                                     (lambda (err) u))))
                         (set! rubi-inert-depth (- rubi-inert-depth 1))
                         r)
                       (loop (cdr es))))))))))
