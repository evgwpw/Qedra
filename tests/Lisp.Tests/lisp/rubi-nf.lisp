; tests/Lisp.Tests/lisp/rubi-nf.lisp — RUBI.NF: одна нормальная форма выражения для Rubi.
; Проверяется, что rubi-nf делает ровно автовычисление языка правил Rubi (Flat/Orderless, числа, основания
; степеней, целые степени произведения, Times[-1, …]) и НЕ делает упрощений (tan остаётся tan,
; скобки не раскрываются, подобные с символьными коэффициентами не собираются).
(load "lib/rubi/nf.lisp")

(define (nf-is e want) (assert-equal (rubi-nf e) want))

(deftest "rubi-nf: числа сворачиваются, единицы и нули уходят"
  (nf-is '(* 2 3 x) '(* 6 x))
  (nf-is '(+ 1/2 1/3 x) '(+ 5/6 x))
  (nf-is '(* 1 x) 'x)
  (nf-is '(+ 0 x) 'x)
  (nf-is '(* 0 x) 0)
  (nf-is '(+ 1 2) 3)
  (nf-is '(* -1 (^ 2 3)) -8))

(deftest "rubi-nf: подобные слагаемые и Times[-1, …]"
  (nf-is '(+ x x) '(* 2 x))
  (nf-is '(+ (* 2 x) (* 3 x)) '(* 5 x))
  (nf-is '(+ x (* -1 x)) 0)
  (nf-is '(- (* 2 x) (* 3 x)) '(* -1 x))
  (nf-is '(- x) '(* -1 x))
  ; с символьными коэффициентами исходник Rubi подобные не собирает — и мы нет
  (nf-is '(+ (* a x) (* b x)) '(+ (* a x) (* b x))))

(deftest "rubi-nf: степени — основания склеиваются, целые степени раскрываются"
  (nf-is '(* x (^ x 2)) '(^ x 3))
  (nf-is '(* (^ x 1/2) (^ x 1/2)) 'x)
  (nf-is '(* (exp x) (exp (* 2 x))) '(^ E (* 3 x)))
  (nf-is '(* (^ x a) (^ x b)) '(^ x (+ a b)))
  (nf-is '(^ (^ x 2) 3) '(^ x 6))
  (nf-is '(^ (* a b) 2) '(* (^ a 2) (^ b 2)))
  ; дробная внешняя степень НЕ сворачивается: (u²)^(1/2) = |u|, а не u
  (nf-is '(^ (^ x 2) 1/2) '(^ (^ x 2) 1/2))
  (nf-is '(^ x 0) 1)
  (nf-is '(^ x 1) 'x))

(deftest "rubi-nf: деление и корни — как автовычисление, без упрощений"
  (nf-is '(/ 1 (* a b)) '(* (^ a -1) (^ b -1)))
  (nf-is '(/ (sin x) (cos x)) '(* (sin x) (^ (cos x) -1)))
  (nf-is '(sqrt 4) 2)
  (nf-is '(sqrt (* 4 x)) '(* 2 (^ x 1/2)))
  (nf-is '(sqrt (* a b)) '(^ (* a b) 1/2)))

; RUBI.TRIG: тригонометрия в rubi-nf — форма ядра (*rubi-trig-nf* #t по умолчанию); тесты головной формы идут при #f
(define (with-trig-nf v f)
  (let ((old *rubi-trig-nf*))
    (set! *rubi-trig-nf* v)
    (unwind-protect (f) (set! *rubi-trig-nf* old))))

(deftest "rubi-nf: тригонометрия в форме ядра (sec -> cos^-1, tan -> sin cos^-1, как math-eval)"
  (with-trig-nf #t
    (lambda ()
      (nf-is '(sec x) '(^ (cos x) -1))
      (nf-is '(^ (csc x) 2) '(^ (sin x) -2))
      (nf-is '(tan x) '(* (sin x) (^ (cos x) -1)))
      (nf-is '(^ (tan x) 2) '(* (^ (sin x) 2) (^ (cos x) -2)))
      (nf-is '(cot x) '(* (cos x) (^ (sin x) -1)))
      (nf-is '(^ (sec x) 1/2) '(^ (^ (cos x) -1) 1/2))
      (nf-is '(* (^ (sec x) 2) (tan x)) '(* (^ (cos x) -3) (sin x)))
      (assert-equal (rubi::nf-acsort (rubi-nf (math-eval "tan(x)^2/sec(x)")))
                    (rubi::nf-acsort (rubi-nf '(/ (^ (tan x) 2) (sec x))))))))

(deftest "rubi-nf: тригонометрия и скобки не трогаются (одна форма — головы Rubi; *rubi-trig-nf* #f)"
 (with-trig-nf #f (lambda ()
  (nf-is '(tan x) '(tan x))
  (nf-is '(sec x) '(sec x))
  (nf-is '(cot x) '(cot x))
  (nf-is '(csc x) '(csc x))
  (nf-is '(* (tan x) (cos x)) '(* (tan x) (cos x)))
  (nf-is '(^ (+ a b) 2) '(^ (+ a b) 2))
  ; ac-norm под единой формой тоже не переписывает sec/cot/csc
  (ac-trig-recip! #f)
  (assert-equal (ac-norm '(sec x)) '(sec x))
  (assert-equal (ac-norm '(^ (cot x) 2)) '(^ (cot x) 2))
  (ac-trig-recip! #t)
  (assert-equal (ac-norm '(sec x)) '(^ (cos x) -1)))))

(deftest "rubi-nf: форма идемпотентна (норма дважды = норма один раз)"
  (for-each
   (lambda (e)
     (assert-equal (rubi-nf (rubi-nf e)) (rubi-nf e)))
   (list '(/ 1 (* a b)) '(* (tan x) (^ (cos x) -2)) '(+ (* 2 (^ x 2)) (* -2 (^ x 2)) y)
         '(sqrt (* 4 (^ x 2))) '(* (exp x) (^ (exp x) -1)) '(+ (/ a b) (/ c d)))))

(deftest "rubi-nf: интегралы, где форма решает (Rubi узнаёт правило)"
  ; флаг включается только на время проверки: по умолчанию единая форма выключена (шаги 2–3 карточки)
  (set! *rubi-nf* #t)
  (ac-trig-recip! #f)
  ; tan и sec остаются головами: правила 4.1/4.2 на них есть, на sin·cos^-1 — нет
  (assert-equal (integrate '(tan x) 'x) '(* -1 (log (cos x))))
  (assert-equal (integrate '(/ 1 (cos x)) 'x)
                '(log (* (+ 1 (sin x)) (^ (cos x) -1))))
  (assert-equal (integrate '(* (sin x) (cos x)) 'x) '(* 1/2 (^ (sin x) 2)))
  (assert-equal (integrate '(/ 1 (+ 1 (^ x 2))) 'x) '(atan x))
  (set! *rubi-nf* #f)
  (ac-trig-recip! #t))


(deftest "rubi-nf: упрощения Rubi не меняют тригонометрическую форму (шаг 3)"
  ; Simp/SimplifyIntegrand не переписывают tan/cot/sec/csc в sin/cos даже ценой «меньшего» выражения
  (assert-equal (rubi::rubi-simplify-integrand '(tan x) 'x) '(tan x))
  (assert-equal (rubi::rubi-simplify-integrand '(^ (sec x) 2) 'x) '(^ (sec x) 2))
  (assert-equal (rubi::rubi-simp '(cot x)) '(cot x))
  ; обычное упрощение (не больше исходного, без тригонометрии) проходит как раньше
  (assert-equal (rubi::rubi-simplify-integrand '(+ x x) 'x) '(* 2 x))
  (assert-equal (rubi::rubi-simp '(+ (* 2 x) (* 3 x))) '(* 5 x)))

; --- RUBI.NF.CONF: конфлюэнтность (tools/rubi/nf-conf.mjs: равные выражения -> одинаковая форма) ---
(deftest "rubi-nf/conf: сократившийся множитель не оставляет литерал 1"
  (nf-is '(* (^ x -1) x y) 'y)
  (nf-is '(* (^ (+ 2 x) -1) (+ 2 x) (^ (+ 3 x) 2)) '(^ (+ 3 x) 2))
  (nf-is '(log (* 2 (^ u -2) (^ u 2))) '(log 2)))

(deftest "rubi-nf/conf: основания, равные с точностью до порядка слагаемых (Plus — Orderless), склеиваются"
  (nf-is '(* (^ (+ a b) -1) (+ b a)) 1)
  (nf-is '(* (^ (+ a (* 2 x)) 2) (^ (+ (* 2 x) a) 3)) '(^ (+ a (* 2 x)) 5)))

(deftest "rubi-nf/conf: (u^a)^n при целом n и символьном a; результат — снова форма (u v)^n раскрыта"
  (nf-is '(^ (^ 2 (* 2 u)) 2) '(^ 2 (* 4 u)))
  (nf-is '(^ (^ x a) 3) '(^ x (* 3 a)))
  (nf-is '(^ (^ (* 2 s) -1/2) 2) '(* 1/2 (^ s -1)))
  ; дробная внешняя степень по-прежнему не сворачивается
  (nf-is '(^ (^ x a) 1/2) '(^ (^ x a) 1/2)))

(deftest "rubi-nf/conf: положительный числовой множитель выходит из нецелой рациональной степени"
  (nf-is '(sqrt (* 2 x)) '(* (^ 2 1/2) (^ x 1/2)))
  (nf-is '(^ (* 2 x) 1/3) '(* (^ 2 1/3) (^ x 1/3)))
  (nf-is '(^ (* 1/2 x) -1/2) '(* (^ 2 1/2) (^ x -1/2)))
  (nf-is '(^ (* 2 a x) 1/2) '(* (^ 2 1/2) (^ (* a x) 1/2)))
  ; x·(2x)^(-1/2) = Sqrt[x]/Sqrt[2] сводится к тому же, что и (x/2)^(1/2)
  ; (порядок множителей — по первому появлению, сопоставитель коммутативный: сравниваем с точностью до порядка)
  (assert-equal (rubi::nf-acsort (rubi-nf '(* x (^ (* 2 x) -1/2)))) (rubi::nf-acsort (rubi-nf '(* (^ 2 -1/2) (^ x 1/2)))))
  ; отрицательный коэффициент и символьный показатель не трогаются
  (nf-is '(^ (* -2 x) 1/2) '(^ (* -2 x) 1/2))
  (nf-is '(^ (* 2 x) n) '(^ (* 2 x) n)))

(deftest "rubi-nf/conf: числа-радикалы приведены к виду исходника Rubi"
  (nf-is '(* 2 (^ 2 -1/2)) '(^ 2 1/2))
  (nf-is '(* 4 (^ 2 -1/2)) '(* 2 (^ 2 1/2)))
  (nf-is '(* 1/2 (^ 2 1/2)) '(^ 2 -1/2))
  (nf-is '(^ 2 3/2) '(* 2 (^ 2 1/2)))
  (nf-is '(^ 8 1/2) '(* 2 (^ 2 1/2)))
  (nf-is '(^ 12 1/2) '(* 2 (^ 3 1/2)))
  (nf-is '(^ 8 1/3) 2)
  (nf-is '(^ 1/2 1/2) '(^ 2 -1/2))
  (nf-is '(* (sqrt 2) (sqrt 2) x) '(* 2 x))
  ; 2^(1/2) остаётся степенью (не алгебраическое число root(...))
  (nf-is '(sqrt 2) '(^ 2 1/2)))

(deftest "rubi-nf/conf: корни из отрицательных рациональных и степени I"
  (nf-is '(sqrt -4) '(* 2 %i))
  (nf-is '(^ -1 -3/2) '%i)
  (nf-is '(* %i %i) -1)
  (nf-is '(^ %i 3) '(* -1 %i)))

(deftest "rubi-nf/conf: расхождения, которые исходник Rubi тоже не сводит, остаются"
  ; нет тригонометрических тождеств; x (x y)^r с символьным произведением и 2^(2+u) против 4·2^u не склеиваются
  ; (при *rubi-trig-nf* #f; в форме ядра sec = 1/cos, это целиком смысл RUBI.TRIG)
  (assert-true (not (equal? (with-trig-nf #f (lambda () (rubi-nf '(sec x)))) (rubi-nf '(/ 1 (cos x))))))
  (assert-equal (with-trig-nf #t (lambda () (rubi-nf '(sec x)))) (rubi-nf '(/ 1 (cos x))))
  (assert-true (not (equal? (rubi-nf '(* x y (^ (* x y) 1/2))) (rubi-nf '(^ (* x y) 3/2)))))
  (assert-true (not (equal? (rubi-nf '(^ 2 (+ 2 u))) (rubi-nf '(* 4 (^ 2 u)))))))

(deftest "rubi-nf/conf: идемпотентность новых форм"
  (for-each
   (lambda (e) (assert-equal (rubi-nf (rubi-nf e)) (rubi-nf e)))
   (list '(sqrt (* 2 x)) '(* 4 (^ 2 -1/2)) '(^ 12 1/2) '(* (^ (+ a b) -1) (+ b a)) '(^ (^ 2 (* 2 u)) 2)
         '(sqrt -4) '(* x (^ (* 2 x) -1/2)) '(^ 8 1/3))))

; --- RUBI.NF.2: инертная тригонометрия ---
(deftest "rubi-nf/2: клаузы Fix/Unify сгенерированы из IUF.m"
  ; таблицы собираются tools/rubi/inert.mjs из IntegrationUtilityFunctions.m; каждая запись несёт
  ; номер строки источника, поэтому таблица проверяема против исходника
  (let* ((fix (filter (lambda (e) (not (equal? (car e) 'unsupported)))
                      (rubi::rubi-inert-table 'fix)))
         (un (filter (lambda (e) (not (equal? (car e) 'unsupported)))
                     (rubi::rubi-inert-table 'unify))))
    (assert-equal (length fix) 57)
    (assert-equal (length un) 75)
    ; 6228 — первая клауза Fix, 6549 — первая Unify, 6484/7294 — терминальные (возвращают u)
    (assert-equal (car (car fix)) "IUF 6228")
    (assert-equal (car (car un)) "IUF 6549")
    (assert-true (member? "IUF 6484" (map car fix)))
    (assert-true (member? "IUF 7294" (map car un)))
    ; четыре клаузы с головой-переменной помечены unsupported, а не выброшены молча
    (assert-equal (length (filter (lambda (e) (equal? (car e) 'unsupported))
                                  (rubi::rubi-inert-table 'fix))) 4)))

(deftest "rubi-nf/2: FixInertTrigFunction по таблице сводит обратные головы"
  ; IUF 6237: csc[v]^m*(c*sin[w])^n -> sin[v]^(-m)*(c*sin[w])^n
  ; (таблица написана на головах: в форме ядра rubi-nf до неё раскладывает csc/sec/tan, поэтому проверка при *rubi-trig-nf* #f)
  (let ((old rubi::*rubi-inert-generated*))
    (rubi::rubi-inert-generated! #t)
    (with-trig-nf #f
      (lambda ()
        ; RUBI.TRIG.4: csc^m теперь совпадает и со степенью sin (m = -k), поэтому таблица доводит произведение до конца:
        ; sin^-2 sin^3 -> sin (раньше результат оставался как после одной клаузы 6237)
        (assert-equal (rubi::rubi-fix-inert-trig-function '(* (^ (csc x) 2) (^ (sin x) 3)) 'x)
                      '(sin x))
        (assert-equal (rubi::rubi-fix-inert-trig-function '(* (^ (sec x) 2) (^ (cos x) 2)) 'x)
                      1)
        ; терминальная клауза 6484: больше нечего переписывать — выражение остаётся собой
        (assert-equal (rubi::rubi-fix-inert-trig-function '(tan x) 'x) '(tan x))))
    (rubi::rubi-inert-generated! old)))

(deftest "rubi-nf/4: prepared-образцы таблицы Unify кэшируются по форме (RUBI.SYM.4)"
  ; ac-build-prepared нормализует образец через ac-norm, а ac-norm смотрит *ac-trig-recip*: в старой
  ; форме (^ (csc v) 2) становится (^ (sin v) -2), в единой csc остаётся головой. Ключ
  ; *rubi-inert-prep* поэтому включает флаг формы; без него первый скомпилированный вариант
  ; переиспользовался в другой форме, сопоставление не срабатывало, и FixInertTrigFunction возвращал
  ; вход без изменений — ответ зависел от порядка обращений (REPORT-RUBI-SYM3.md, §5.6).
  (let* ((pat '(* (^ (csc ?v) 2) (^ (csc ?v) 3)))
         (old (ac-trig-recip)))
    (ac-trig-recip! #t)
    (let ((p1 (rubi::rubi-inert-prepared pat)))
      (ac-trig-recip! #f)
      (let ((p2 (rubi::rubi-inert-prepared pat)))
        (assert-true (contains-sym? (car p1) 'sin))      ; старая форма: csc свёрнут в sin^-1
        (assert-true (not (contains-sym? (car p2) 'sin))) ; единая: csc остаётся головой
        (assert-true (not (equal? p1 p2)))))
    (ac-trig-recip! old))
  ; rubi-form-sync пересобирает кэш вместе с индексом: после смены формы он пуст
  (let ((oldn *rubi-nf*))
    (set! *rubi-nf* #f)
    (rubi::rubi-form-sync)
    (set! *rubi-nf* #t)
    (rubi::rubi-form-sync)          ; смена формы -> кэш пуст
    (rubi::rubi-fix-inert-trig-function '(^ (csc x) 4) 'x)
    (assert-true (> (hash-count rubi::*rubi-inert-prep*) 0))
    (set! *rubi-nf* #f)
    (rubi::rubi-form-sync)          ; снова смена формы -> кэш пуст
    (assert-equal 0 (hash-count rubi::*rubi-inert-prep*))
    (set! *rubi-nf* oldn)))

; --- RUBI.NF.CH48: классы потерь единой формы в главах 4 и 8 ---
; (1) глава 8.9: образцы .nf.lisp записаны именами исходника Rubi (ProductLog); подмена ставила их в правило
; без переименования в голову диалекта lambert_w — правила 8.9 не совпадали вовсе.
(deftest "rubi-nf/ch48: ProductLog из .nf.lisp совпадает с lambert_w (8.9)"
  (let ((old *rubi-nf*) (old-lim rubi::rubi-time-limit))
    (set! rubi::rubi-time-limit 30.0)
    (set! *rubi-nf* #t)
    (rubi::rubi-form-sync)
    (let* ((e (math-read "lambert_w(a*x)^2/x^4"))
           (r (rubi-integrate e 'x)))
      (assert-true (not (equal? r 'unknown)))
      (assert-true (not (contains-sym? r 'integrate)))
      (assert-true (int-check r e 'x)))
    (set! rubi::rubi-time-limit old-lim)
    (set! *rubi-nf* old)
    (rubi::rubi-form-sync)))

; (2) глава 4: под #t sec/csc/cot остаются головами, а правила 4.1.x/4.2.x записаны для cos^-n/sin^-n;
; смешанные формы (sec/csc вместе с sin/cos) отказывали — шлюз после перебора переводит головы в степени.
(deftest "rubi-nf/ch48: sec/csc вместе с sin/cos берутся шлюзом reciprocal-голов"
  (assert-equal (rubi::rubi-recip-to-powers '(^ (sec x) 2)) '(^ (cos x) -2))
  (assert-equal (rubi::rubi-recip-to-powers '(csc x)) '(^ (sin x) -1))
  (assert-equal (rubi::rubi-recip-to-powers '(+ (^ (cot x) 3) y)) '(+ (^ (tan x) -3) y))
  (let ((old *rubi-nf*) (old-lim rubi::rubi-time-limit))
    (set! *rubi-nf* #t)
    (set! rubi::rubi-time-limit 30.0)
    (rubi::rubi-form-sync)
    (assert-true (not (rubi::rubi-recip-gateway? '(^ (sec x) 2))))
    (assert-true (rubi::rubi-recip-gateway? '(* (^ (sec x) 2) (sin x))))
    (for-each
     (lambda (s)
       (let* ((e (math-read s)) (r (rubi-integrate e 'x)))
         (assert-true (not (equal? r 'unknown)))
         (assert-true (int-check r e 'x))))
     (list "sec(c + d*x)^4/(a*sin(c + d*x) + a)^(5/2)"
           "(a*sin(c + d*x) + a)^(3/2)*csc(c + d*x)^2"))
    (set! rubi::rubi-time-limit old-lim)
    (set! *rubi-nf* old)
    (rubi::rubi-form-sync)))

; --- RUBI.GEN.3: отличия единой формы из <файл>.nf.lisp реально применяются ---
; GEN.2 применял их до цикла загрузки (список был пуст), а каждый файл ещё и перезаписывал список, поэтому при
; *rubi-nf* #t движок работал со старыми образцами — «быстрый» холодный старт был быстрым именно из-за этого.
(define (rubi-gen3-nf-same? o r)
  ; запись .nf.lisp: (id образец головы мин-множителей показатели); запись правила: те же поля 2, 6, 7, 8
  ; RUBI.TRIG: образцы с головами sec/csc/tan/cot приводятся к форме ядра при загрузке (rubi-renf-rules), а поля индекса
  ; пересчитываются, поэтому у них сравнивается образец после rubi-nf
  (if (and *rubi-trig-nf* (rubi::rubi-pat-trig-head? (nth o 1)))
      (equal? (rubi-nf (nth o 1)) (nth r 2))
      (and (equal? (nth o 1) (nth r 2))
           (equal? (nth o 2) (nth r 6))
           (equal? (nth o 3) (nth r 7))
           (equal? (nth o 4) (nth r 8)))))

(deftest "rubi-nf/gen3: отличия единой формы из <файл>.nf.lisp применяются"
  (let ((oldn *rubi-nf*))
    ; базовая форма загружена целиком и снята: id -> образец
    (set! *rubi-nf* #f)
    (rubi::rubi-form-sync)
    (rubi::rubi-ensure)
    (let ((base (make-hash)))
      (for-each (lambda (r) (hash-set! base (nth r 1) (nth r 2))) rubi::*rubi-rules*)
      ; переключение в единую форму: отличия применяются при загрузке, кэш отличий пуст
      (set! *rubi-nf* #t)
      (rubi::rubi-form-sync)
      (assert-equal '() rubi::*rubi-nf-overrides*)
      (let ((rules (make-hash)))
        (for-each (lambda (r) (hash-set! rules (nth r 1) r)) rubi::*rubi-rules*)
        ; читаем все .nf.lisp сами: каждая запись должна совпасть с образцом правила в памяти
        (set! rubi::*rubi-nf-overrides* '())
        (for-each (lambda (f) (rubi::rubi-load-nf-file f)) rubi::rubi-rule-files)
        (let* ((entries rubi::*rubi-nf-overrides*)
               (res (let loop ((l entries) (bad 0) (miss 0))
                      (if (null? l)
                          (list bad miss)
                          (let ((o (car l)) (r (hash-ref rules (car (car l)) #f)))
                            (cond ((not r) (loop (cdr l) bad (+ miss 1)))
                                  ((rubi-gen3-nf-same? o r) (loop (cdr l) bad miss))
                                  (else (loop (cdr l) (+ bad 1) miss))))))))
          (assert-true (> (length entries) 1500))
          (assert-equal 0 (car res))    ; несовпадений образцов/полей — 0
          (assert-equal 0 (cadr res)))  ; правил с id из .nf.lisp, которых нет в памяти, — 0
        (set! rubi::*rubi-nf-overrides* '()))
      ; обратно на #f: образцы снова базовые (снимок до переключения)
      (set! *rubi-nf* #f)
      (rubi::rubi-form-sync)
      (let ((bad (let loop ((l rubi::*rubi-rules*) (n 0))
                   (if (null? l)
                       n
                       (loop (cdr l)
                             (if (equal? (nth (car l) 2) (hash-ref base (nth (car l) 1) #f)) n (+ n 1)))))))
        (assert-equal 0 bad)))
    (set! *rubi-nf* oldn)
    (rubi::rubi-form-sync)))

(deftest "rubi-nf/2: Log[E] сворачивается в готовом ответе"
  ; В правых частях Rubi пишет Log[F] при F = E; исходник Rubi вычисляет это в 1. Если не свернуть,
  ; ответы единой формы приходят как Ei(x·log E) и erfi(x·√log E) — simplify(log E) их не берёт.
  (assert-equal (rubi::rubi-fold-log-e '(* -1 (gamma 0 (* -1 x (log E)))))
                '(* -1 (gamma 0 (* -1 x 1))))
  ; в движке результат сразу идёт в simplify, который убирает единицу: -Γ(0, -x)
  (assert-equal (rubi::rubi-fold-log-e '(* (erfi (* x (^ (log E) 1/2))) (^ (log E) -1/2)))
                '(* (erfi (* x (^ 1 1/2))) (^ 1 -1/2)))
  ; log другого основания не трогается
  (assert-equal (rubi::rubi-fold-log-e '(log (* a x))) '(log (* a x))))


