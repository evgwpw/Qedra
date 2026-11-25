; rubi/engine.lisp — движок правил Rubi (RUBI.1): порядок правил, индексация, int-check.
; Правила генерируются tools/rubi в lib/rubi/rules и грузятся лениво при первом вызове.
(module rubi
  (export rubi-integrate rubi-integrate-form rubi-integrate-within rubi-trace-run))

; общий бюджет вызова (с загрузкой правил), с: стенд убивает задачу на 5 с и перезапускает процесс,
; поэтому движок должен вернуть unknown раньше — иначе каждая отказная задача = TIMEOUT + холодный старт.
(define rubi-time-limit 4.0)
(define rubi-max-depth 32)
(define *rubi-rules* '())
; корзины по обязательным головам образца (RUBI.SPEED) — не путать с *rubi-index* (RUBI.INDEX, флаг включения)
(define *rubi-hindex* (make-hash))
(define *rubi-prepared* (make-hash))  ; id → (np ip vars): образец компилируется при первом использовании
(define *rubi-fixed* (make-hash))     ; id → (cond . rhs) с переписанными именами Mathematica
(define *rubi-cond-fns* (make-hash))  ; id → замыкание условия: (lambda (binds) ...) без eval на кандидата
(define *rubi-failed* (make-hash))    ; выражение → (таблица id → #t): неудачи одного вызова rubi-integrate
(define *rubi-cache-hits* 0)          ; сколько раз кэш неудач сэкономил попытку
(define *rubi-cands2* (make-hash))    ; выражение → кандидаты, прошедшие отсев по головам и форме (RUBI.S8)
(define *rubi-cands* (make-hash))     ; выражение → список кандидатов (в пределах вызова)
(define *rubi-errors* (make-hash))    ; текст ошибки вычисления правила → число (диагностика)
(define *rubi-loaded* #f)
(define *rubi-depth* 0)
(define *rubi-stack* '())
(define *rubi-last-reason* #f)
(define *rubi-last-rule* #f)
(define *rubi-tries* 0)
(define *rubi-ord* 0)
(define rubi-rule-files '())

; RUBI.9: профиль по фазам. Включается флагом *rubi-prof*; в обычной работе цена — одна проверка #f.
; Времена инклюзивные: eval включает вложенные вызовы, match и check — листовые фазы.
; eval-self считается как «своё время минус вложенные вызовы»; у вызова, прерванного бюджетом,
; стек не разматывается и self выходит отрицательным — такие замеры годны только для завершённых задач.
(define *rubi-prof* #f)
(define *rubi-p-match* 0)
(define *rubi-p-eval* 0)
(define *rubi-p-check* 0)
(define *rubi-p-matches* 0)
(define *rubi-p-evals* 0)
(define *rubi-p-checks* 0)
(define *rubi-p-calls* 0)
; для eval: сумма времени всех вызовов (sum) и своё время за вычетом вложенных (self)
(define *rubi-p-eval-sum* 0)
(define *rubi-p-eval-self* 0)
; RUBI.13: учёт вычислений условий правил — сколько вызовов, сколько времени, самые медленные.
(define *rubi-p-cond* 0)
(define *rubi-cond-calls* 0)
(define *rubi-cond-slow* '())
(define *rubi-cond-slow-limit* 5)
(define *rubi-matched* '())
; RUBI.SPEED (шаг 1): распределение исходов проверки ответа (simplify/together/numeric/bad/skip) и
; счётчики кэша кандидатов на выражение — только под *rubi-prof*, в обычном режиме не считаются.
(define *rubi-chk-how* (make-hash))
; RUBI.CH567.2: диагностика причин отказа int-check — при *rubi-chk-trace* сюда складываются отвергнутые
; кандидаты задачи: список (правило ответ подынтегральное). Флаг по умолчанию #f, на поведение движка не
; влияет (только запись); чистит список вызывающий (tools/rubi/check-diag.lisp).
(define *rubi-chk-trace* #f)
(define *rubi-chk-log* '())
(define *rubi-p-candhit* 0)
(define *rubi-p-candmiss* 0)
(define *rubi-p-candn* 0)
; Этап C: мемоизация «выражение → результат | unknown» в пределах вызова, журнал причин отказа;
; настенные 5 с — единственный реальный бюджет (см. ниже про предел попыток).
(define *rubi-memo* (make-hash))
(define *rubi-fail-reasons* '())
; Предел попыток сопоставления на задачу — только страховка от бесконечного перебора, а не бюджет.
; Замер (2026-11-08): задача t_1_1_1_3/34 берётся после **6 215** попыток за 414 мс — прежние 5 000
; отсекали готовый ответ, а 3 000 на пилоте стоили 61 OK. Самая быстрая наблюдённая скорость —
; ≈15 000 попыток/с, значит 5 с настенного бюджета позволяют ≈75 000 попыток: 100 000 заведомо
; выше и внутри бюджета не срабатывает.
(define *rubi-tries-limit* 100000)
; EX.EXPLAIN: журнал шагов правил Rubi (рамка rubi-step). #f — рамки не пишутся (ни в steps, ни в attempts):
; объяснение отказа Rubi остаётся, но перебор правил (сколько и каких успело до бюджета) не зависит от скорости
; машины. Движок и проверки не меняются, пишется только журнал.
(define *rubi-step-log* #t)
; Семантика Rubi: первое правило, чьи образец и условие подошли, окончательное — даже если его правая
; часть дала `unknown` (вложенный Int отказал). Перебор следующего кандидата — только после ошибки правой
; части или провала int-check. Флаг оставлен, чтобы сравнивать с прежним поведением одним set!.
(define *rubi-first-rule-final* #t)

; ---------- RUBI.BACKTRACK (шаг 0): счётчики откатов ----------
; Откат — переход к следующему кандидату после того, как подошедшее по образцу и условию правило не дало принятого
; ответа (int-check, метка отказа в правой части, ошибка вычисления). Счётчики нужны для замера: сколько ответов
; получено через откат и по каким правилам, сколько откатов уходит в главу 9. Стоимость — hash-ref на откат,
; на результат не влияют.
(define *rubi-bt-n* 0)                   ; откатов за задачу
(define *rubi-bt-ne* (make-hash))        ; выражение -> #t: для него уже был откат
(define *rubi-bt-win* '())               ; id правила -> сколько ответов дано после отката на том же выражении
(define *rubi-bt-wins* 0)
(define *rubi-bt-9x* '())                ; id правила главы 9, к которому пришёл откат -> сколько раз
(define *rubi-bt-9x-n* 0)
(define *rubi-bt-9x-task* #f)            ; в этой задаче откат уходил в главу 9
(define *rubi-bt-no9-ne* (make-hash))    ; выражение -> #t: правило 1–8 отказало, глава 9 для него закрыта
(define (rubi-bt-reset)
  (set! *rubi-bt-n* 0)
  (set! *rubi-bt-ne* (make-hash))
  (set! *rubi-bt-win* '())
  (set! *rubi-bt-wins* 0)
  (set! *rubi-bt-9x* '())
  (set! *rubi-bt-9x-n* 0)
  (set! *rubi-bt-9x-task* #f)
  (set! *rubi-bt-no9-ne* (make-hash))
  (set! *rubi-bt-9x-base* (make-hash))
  (set! *rubi-bt-ne-n* (make-hash))
  (set! *rubi-bt-ne-max* 0)
  (set! *rubi-bt-ne-max-expr* #f))
; счётчик в alist «ключ -> число» (без set-cdr!: пересборка, как в rubi-note-reason)
(define (rubi-bt-bump alst k)
  (let* ((old (assoc k alst))
         (n (+ 1 (if old (cdr old) 0))))
    (cons (cons k n) (filter (lambda (p) (not (equal? (car p) k))) alst))))
; id правила вида "Rubi 1.1.2.5 #11" или "9.3 #17" — номер главы
(define (rubi-rule-chapter id)
  (let ((s (if (string-contains? id "Rubi ") (substring id 5 (string-length id)) id)))
    (if (> (string-length s) 0) (substring s 0 1) "")))
; отметить откат: id — отказавшее правило, nx — правило, к которому переходим (первый из оставшихся кандидатов)
(define (rubi-bt-fallback ne id nx)
  (set! *rubi-bt-n* (+ *rubi-bt-n* 1))
  (hash-set! *rubi-bt-ne* ne #t)
  (let ((k (+ 1 (hash-ref *rubi-bt-ne-n* ne 0))))
    (hash-set! *rubi-bt-ne-n* ne k)
    (if (> k *rubi-bt-ne-max*)
        (begin (set! *rubi-bt-ne-max* k) (set! *rubi-bt-ne-max-expr* ne))))
  ; RUBI.BACKTRACK: правило своей главы отказало — перебор главы 9 для этого подвыражения ограничен
  (if (and *rubi-bt-no9* (not (equal? (rubi-rule-chapter id) "9")))
      (hash-set! *rubi-bt-no9-ne* ne #t))
  ; RUBI.BACKTRACK: начало перебора главы 9 на этом подвыражении — от него считаем потраченные попытки
  (if (and nx (equal? (rubi-rule-chapter nx) "9") (not (hash-ref *rubi-bt-9x-base* ne #f)))
      (hash-set! *rubi-bt-9x-base* ne *rubi-tries*))
  (if (and nx (equal? (rubi-rule-chapter nx) "9"))
      (begin (set! *rubi-bt-9x-n* (+ *rubi-bt-9x-n* 1))
             (set! *rubi-bt-9x* (rubi-bt-bump *rubi-bt-9x* nx))
             (set! *rubi-bt-9x-task* #t)))
  #t)
; ответ на выражении ne дало правило id; если до этого на ne был откат — это «ответ через откат»
(define (rubi-bt-win ne id)
  (if (hash-ref *rubi-bt-ne* ne #f)
      (begin (set! *rubi-bt-wins* (+ *rubi-bt-wins* 1))
             (set! *rubi-bt-win* (rubi-bt-bump *rubi-bt-win* id))))
  #t)

; ---------- RUBI.BACKTRACK (шаг 1): ограничение отката ----------
; Замер шага 0 (срезы 1.1 и 4): откат нужен — на slice-4 через него получено 5 057 ответов из 671 ok, —
; но на задачи у края бюджета откат превращается в перебор главы 9 (подстановки): rubi-ell1/3 перебирает
; 9.x на одном подвыражении 26 тыс. попыток и ответа не находит, хотя при ограничении решается за 16 с.
; В Rubi такой цепочки нет: правило окончательно, а правило с 0^(-1) в правой части не прошло бы условие.
; Ограничение: на подвыражении, где правило своей главы уже подошло и отказало, перебор главы 9 не должен
; стоить больше *rubi-bt-9x-tries* попыток сопоставления — дальше кандидаты 9.x пропускаются.
; 0 — предел выключен (поведение до RUBI.BACKTRACK, для сравнения «как было»); *rubi-bt-no9* #f — то же.
; Пределы «б» (число откатов на подвыражение) и «в» (жёсткое закрытие главы 9) проверены и отклонены:
; см. REPORT-RUBI-BACKTRACK.md (потери 67 задач slice-4 и 17 задач slice-1.1).
(define *rubi-bt-no9* #t)
(define *rubi-bt-9x-tries* 5000)
(define *rubi-bt-9x-base* (make-hash))    ; выражение -> число попыток на начале перебора главы 9

; замер: откаты на подвыражении (сколько и на каком именно — для отчёта и разбора)
(define *rubi-bt-ne-n* (make-hash))
(define *rubi-bt-ne-max* 0)
(define *rubi-bt-ne-max-expr* #f)

; Пропустить кандидата главы 9: подвыражение уже потратило на перебор 9.x больше предела попыток.
(define (rubi-bt-9x-skip ne id)
  (and *rubi-bt-no9*
       (> *rubi-bt-9x-tries* 0)
       (equal? (rubi-rule-chapter id) "9")
       (hash-ref *rubi-bt-no9-ne* ne #f)
       (> (- *rubi-tries* (hash-ref *rubi-bt-9x-base* ne 0)) *rubi-bt-9x-tries*)))



; Журнал причин отказа: alist (причина . число), чтобы гистограмму можно было напечатать в профиле.
(define (rubi-note-reason why)
  (let* ((old (assoc why *rubi-fail-reasons*))
         (n (+ 1 (if old (cdr old) 0))))
    (set! *rubi-fail-reasons*
          (cons (cons why n)
                (filter (lambda (p) (not (equal? (car p) why))) *rubi-fail-reasons*)))))

(define (rubi-prof-reset)
  (set! *rubi-p-match* 0)
  (set! *rubi-p-eval* 0)
  (set! *rubi-p-check* 0)
  (set! *rubi-p-matches* 0)
  (set! *rubi-p-evals* 0)
  (set! *rubi-p-checks* 0)
  (set! *rubi-p-calls* 0)
  (set! *rubi-p-eval-sum* 0)
  (set! *rubi-p-eval-self* 0)
  (set! *rubi-p-cond* 0)
  (set! *rubi-p-prep* 0)
  (set! *rubi-p-norm* 0)
  (set! *rubi-p-inert* 0)
  (set! *rubi-p-inertn* 0)
  (set! *rubi-p-deact* 0)
  (set! *rubi-p-deactn* 0)
  (set! *rubi-p-step* 0)
  (set! *rubi-p-inner* 0)
  (set! *rubi-p-rhs* 0)
  (set! *rubi-p-err* 0)
  (set! *rubi-p-scan* 0)
  (set! *rubi-p-idxn* 0)
  (set! *rubi-p-int-acc* 0)
  (set! *rubi-cond-calls* 0)
  (set! *rubi-cond-timeouts* 0)
  (set! *rubi-cond-slow* '())
  (set! *rubi-chk-how* (make-hash))
  (set! *rubi-p-candhit* 0)
  (set! *rubi-p-candmiss* 0)
  (set! *rubi-p-candn* 0)
  (set! *rubi-matched* '()))

; Топ частот по хэш-таблице «ключ → число»: ошибки правил и вызовы заглушек — гистограммы
; для выбора того, что реализовывать следующим (этап D).
(define (rubi-hist-top h n)
  (take (sort (map (lambda (k) (cons (hash-ref h k 0) k)) (hash-keys h))
              (lambda (a b) (> (car a) (car b))))
        n))

(define (rubi-error-top n) (rubi-hist-top *rubi-errors* n))

(define (rubi-prof-data)
  (list (cons 'calls *rubi-p-calls*)
        (cons 'matches *rubi-p-matches*)
        (cons 'match-us *rubi-p-match*)
        (cons 'evals *rubi-p-evals*)
        (cons 'eval-us *rubi-p-eval*)
        (cons 'eval-self *rubi-p-eval-self*)
        (cons 'checks *rubi-p-checks*)
        (cons 'check-us *rubi-p-check*)
        (cons 'prep-us *rubi-p-prep*)
        (cons 'norm-us *rubi-p-norm*)
        (cons 'inert-us *rubi-p-inert*)
        (cons 'inert-n *rubi-p-inertn*)
        (cons 'deact-us *rubi-p-deact*)
        (cons 'deact-n *rubi-p-deactn*)
        (cons 'step-us *rubi-p-step*)
        (cons 'inner-us *rubi-p-inner*)
        (cons 'rhs-us *rubi-p-rhs*)
        (cons 'err-us *rubi-p-err*)
        (cons 'scan-us *rubi-p-scan*)
        (cons 'idx-n *rubi-p-idxn*)
        (cons 'cond-calls *rubi-cond-calls*)
        (cons 'chk-how (rubi-hist-top *rubi-chk-how* 6))
        (cons 'cand-hit *rubi-p-candhit*)
        (cons 'cand-miss *rubi-p-candmiss*)
        (cons 'cand-n *rubi-p-candn*)
        (cons 'cond-us *rubi-p-cond*)
        (cons 'cond-timeouts *rubi-cond-timeouts*)
        (cons 'cond-slow *rubi-cond-slow*)
        (cons 'fail-reasons *rubi-fail-reasons*)
        (cons 'tries *rubi-tries*)
        (cons 'errors (rubi-error-top 20))
        (cons 'stubs (rubi-hist-top rubi::*rubi-stub-calls* 20))
        (cons 'matched *rubi-matched*)))

; RUBI.S16: образцы с Sqrt/Exp приводятся к степеням так же, как выражение (rubi-int-body: головы, (u^p)^q,
; ac-norm): раньше образец (/ 1 (sqrt (+ a (* b x^2)))) оставался с головой sqrt, а выражение к тому времени уже
; было (^ u -1/2) - 505 правил главы 1 (1.1.2.1 #16-#18 = ∫1/sqrt(a + b x^2) и др.) не срабатывали никогда;
; головы sqrt/exp также попадали в обязательные головы индекса, которых в выражении нет.
(define (rubi-pat-normalize pat)
  (if *rubi-nf*
      ; RUBI.NF: образец нормализуется ТОЙ ЖЕ функцией формы, что и выражение (одна форма на обе стороны
      ; сопоставления): головы sqrt/exp/I, `/`→^-1, свёртка чисел, склейка оснований, целая степень произведения
      (rubi-nf pat)
      (if (rubi-sqrt-head? pat)
          (ac-strip-units (rubi-collapse-pow (ac-norm (rubi-normalize-heads pat))))
          pat)))

(define (rubi-add-rule id pat0 cond rhs)
  (set! *rubi-rules*
        (let ((pat (rubi-pat-normalize pat0)))
          (cons (list *rubi-ord* id pat cond rhs #f (rubi-pat-heads pat '())
                      (rubi-pat-min-factors pat) (rubi-pat-exponents pat '())
                      #f (not (null? cond)))
                *rubi-rules*)))
  (set! *rubi-ord* (+ *rubi-ord* 1)))

; RUBI.6.2: файлы правил - данные, а не вызовы rubi-add-rule на каждое правило, и в двух частях:
;   <файл>.lisp       (rubi-rules-data "файл" '(("id" образец условие? головы мин-множителей показатели) ...))
;   <файл>.body.lisp  (rubi-bodies-data '(("id" условие правая-часть) ...))
;   <файл>.nf.lisp    (rubi-rules-nf-data '((id образец головы мин-множителей показатели) ...)) — только те
;                     правила, у которых образец единой формы (#t, rubi-nf) отличается от старой (#f, ac-norm);
;                     файл читается лишь при *rubi-nf* #t (tools/rubi/precompute.mjs).
; RUBI.GEN.2: холодный старт при #t раньше был 8,8 с против 2,95 с при #f: под #t все 8506 образцов
; нормализовались при загрузке (rubi-rules-data) и ещё раз в rubi-build-index, и задача на стенде убивалась
; таймаутом 5 с. Теперь обе формы предвычислены: базовая (старая) — как раньше, отличия #t — в <файл>.nf.lisp,
; и при #t образец уже нормализован (в rubi-build-index он же идёт как «образец для индекса»).
; Образец нормализован (rubi-pat-normalize), поля индекса вычислены tools/rubi/precompute.mjs; условие? - есть ли
; условие (#t/#f). Условия и правые части занимают ≈ 70 % текста, но нужны только правилам, чей образец подошёл,
; поэтому файл с телами читается при первом обращении к любому его правилу (rubi-fixed, rubi-cond-fn).
; Запись правила: (порядок id образец условие правая-часть подготовленный головы мин-множителей показатели
; файл условие?); у правил из rubi-add-rule (тесты) условие и правая часть лежат в записи, файл = #f.
; Порядок и учёт *rubi-ord* те же, что у rubi-add-rule.
; RUBI.CH8: головы спецфункций. Образцы правил 2.x/8.x записаны именами Mathematica (ProductLog, Erfc, FresnelS,
; SinIntegral, ExpIntegralEi, ...), а вход и ответы — головами диалекта (lambert_w, erfc, Si, Ei, ...), поэтому
; правила на такие головы не срабатывали вовсе (343 задачи гл. 8 с LambertW). Единые имена — те, что печатают обёртки
; правых частей (utils.lisp: rubi-fresnel-s → fresnel_s, rubi-sin-integral → sin_integral, ...): образцы переводятся
; при загрузке (*rubi-head-alias-pat*), вход — в rubi-integrate* (*rubi-head-alias-in*).
(define *rubi-head-alias-pat*
  '((ProductLog . lambert_w) (Erfc . erfc) (Erfi . erfi) (FresnelS . fresnel_s) (FresnelC . fresnel_c)
    (SinIntegral . sin_integral) (CosIntegral . cos_integral) (SinhIntegral . sinh_integral)
    (CoshIntegral . cosh_integral) (ExpIntegralEi . exp_integral_ei) (ExpIntegralE . exp_integral_e)
    (LogIntegral . log_integral) (LogGamma . log_gamma) (PolyGamma . poly_gamma)))
(define *rubi-head-alias-in*
  '((LambertW . lambert_w) (lambertw . lambert_w) (Si . sin_integral) (Ci . cos_integral) (Shi . sinh_integral)
    (Chi . cosh_integral) (Ei . exp_integral_ei) (li . log_integral) (expint . exp_integral_e)
    (fresnels . fresnel_s) (fresnelc . fresnel_c) (loggamma . log_gamma) (polygamma . poly_gamma)))
; переименование голов (car списков) по таблице; (quote ...) не трогается
(define (rubi-rename-heads f tbl)
  (cond ((not (pair? f)) f)
        ((equal? (car f) 'quote) f)
        (else (let ((a (and (symbol? (car f)) (assoc (car f) tbl))))
                (cons (if a (cdr a) (rubi-rename-heads (car f) tbl))
                      (map (lambda (g) (rubi-rename-heads g tbl)) (cdr f)))))))
(define (rubi-rename-head-names l tbl)
  (map (lambda (s) (let ((a (and (symbol? s) (assoc s tbl)))) (if a (cdr a) s))) l))

(define (rubi-rules-data file entries)
  (let loop ((l entries) (rules *rubi-rules*) (ord *rubi-ord*))
    (if (null? l)
        (begin (set! *rubi-rules* rules) (set! *rubi-ord* ord))
        (let ((e (car l)))
          (loop (cdr l)
                (cons (let ((p0 (rubi-rename-heads (cadr e) *rubi-head-alias-pat*)))
                        ; RUBI.GEN.2: поля (образец, головы, мин. число множителей, показатели) предвычислены
                        ; tools/rubi/precompute.mjs для обеих форм, поэтому при загрузке ничего не считается:
                        ; образцы единой формы (#t) приходят отдельным файлом <файл>.nf.lisp
                        ; (rubi-apply-nf-overrides). Раньше под #t здесь нормализовались все 8506 образцов —
                        ; холодный старт 8,8 с против 2,95 с при #f.
                        (list ord (car e) p0 #f #f #f
                              (let ((hs (nth e 3)))
                                (if (pair? hs) (rubi-rename-head-names hs *rubi-head-alias-pat*) hs))
                              (nth e 4) (nth e 5) file (caddr e)))
                      rules)
                (+ ord 1))))))

; RUBI.GEN.2: <файл>.nf.lisp — правила, у которых образец единой формы (#t) отличается от старой (#f).
; Собираем их в *rubi-nf-overrides* и после загрузки всех файлов подменяем в записях правил (порядок полей тот же).
; RUBI.GEN.3: каждый .nf.lisp ДОБАВЛЯЕТ записи, а не перезаписывает список: раньше здесь стояло set!, и после
; цикла загрузки в *rubi-nf-overrides* оставались записи только последнего файла (а применялись они вообще до
; цикла, когда список был пуст) — при #t движок работал со старыми образцами, и «быстрый» холодный старт был
; быстрым именно потому, что отличия не применялись.
(define *rubi-nf-overrides* '())   ; ((id образец головы мин-множителей показатели) ...)
; RUBI.NF.CH48: образцы в .nf.lisp тоже записаны именами Mathematica (ProductLog, ...) — как и базовые.
; Раньше подмена ставила такой образец в правило без rubi-rename-heads, и голова правила снова становилась
; ProductLog: правило 8.9 #37 переставало совпадать с lambert_w (при #t глава 8.9 — 198 потерь).
(define (rubi-rules-nf-data entries)
  (set! *rubi-nf-overrides*
        (append (map (lambda (e)
                       (list (car e)
                             (rubi-rename-heads (nth e 1) *rubi-head-alias-pat*)
                             (let ((hs (nth e 2)))
                               (if (pair? hs) (rubi-rename-head-names hs *rubi-head-alias-pat*) hs))
                             (nth e 3) (nth e 4)))
                     entries)
                *rubi-nf-overrides*)))
(define (rubi-apply-nf-overrides)
  (if (null? *rubi-nf-overrides*)
      #f
      (let ((h (make-hash)))
        (for-each (lambda (o) (hash-set! h (car o) o)) *rubi-nf-overrides*)
        (set! *rubi-rules*
              (map (lambda (r)
                     (let ((o (hash-ref h (nth r 1) #f)))
                       (if o
                           (list (nth r 0) (nth r 1) (nth o 1) (nth r 3) (nth r 4) (nth r 5)
                                 (nth o 2) (nth o 3) (nth o 4) (nth r 9) (nth r 10))
                           r)))
                   *rubi-rules*))
        (set! *rubi-nf-overrides* '()))))

; файл отличий есть не у каждого правила-файла (только там, где формы различаются) — отсутствие не ошибка
(define (rubi-load-nf-file f)
  (try (load (string-append lib-dir "rubi/rules/" f ".nf.lisp"))
       (lambda (e) (if (string-contains? (to-string e) "файл не найден") #f (error (to-string e))))))

(define *rubi-bodies* (make-hash))          ; id -> (условие . правая-часть) из прочитанных <файл>.body.lisp
(define *rubi-bodies-loaded* (make-hash))   ; файл -> #t
(define (rubi-bodies-data entries)
  (for-each (lambda (e) (hash-set! *rubi-bodies* (car e) (cons (cadr e) (caddr e)))) entries))
(define (rubi-load-bodies file)
  (if (not (hash-ref *rubi-bodies-loaded* file #f))
      (begin (hash-set! *rubi-bodies-loaded* file #t)
             (load (string-append lib-dir "rubi/rules/" file ".body.lisp")))))


; Имена Mathematica, попавшие в сгенерированные условия и правые части без перевода:
; not-equal (!=), part ([[i]]), diff (D[u,x] — у нас порядок аргументов обратный).
; Переписываются в приватные обёртки Rubi; (quote ...) не трогается.
(define (rubi-fix-names f)
  (cond ((symbol? f)
         (cond ((equal? f 'not-equal) 'rubi::rubi-not-equal)
               ((equal? f 'part) 'rubi::rubi-part)               ((equal? f 'diff) 'rubi::rubi-diff)
               ((equal? f 'Apart) 'rubi::rubi-apart)
               ((equal? f 'SmartApart) 'rubi::rubi-smart-apart)
               (else f)))
        ((pair? f)
         (cond
           ; Ветвь `If[условие, результат, неприменимо]` правой части: генератор записал её как 'unknown.
           ; Это «правило не сработало» (пробуем следующее), а не отказ вложенного Int — иначе правила
           ; 1.4.1 #19/#21/#22 (проверка Pp, Qq) обрывают перебор раньше 1.1.1.5–1.1.1.7: ∫(a+b*x)(a*c-b*c*x)^4.
           ((equal? f '(quote unknown)) '(quote rubi-no-rule))
           ((equal? (car f) 'quote) f)
           (else (cons (rubi-fix-names (car f)) (map rubi-fix-names (cdr f))))))
        (else f)))

; RUBI.2c: компиляция образца при загрузке занимала заметную долю старта — теперь при первом обращении.
; профиль: время первой подготовки правила (компиляция образца, условия, переписывание имён)
(define *rubi-p-prep* 0)
(define *rubi-p-norm* 0)    ; профиль: нормализация выражения в rubi-int
(define *rubi-p-inert* 0)   ; профиль: инертная нормализация (шлюз Fix+Unify) и число её вызовов/кэш-попаданий
(define *rubi-p-inertn* 0)
(define *rubi-p-deact* 0)   ; профиль: DeactivateTrig (условие 4.1.0.1 #1) — время и число вызовов
(define *rubi-p-deactn* 0)
(define *rubi-p-step* 0)    ; профиль: рамка with-step за вычетом тела
(define *rubi-p-inner* 0)   ; профиль: тело with-step (вызов правой части)
(define (rubi-prep-note t0)
  (if t0 (set! *rubi-p-prep* (+ *rubi-p-prep* (- (clock-us) t0)))))

(define (rubi-prepared r)
  (let ((id (nth r 1)))
    (or (hash-ref *rubi-prepared* id #f)
        (let* ((t0 (and *rubi-prof* (clock-us)))
               ; RUBI.FUZZ: деление в образце переписывается в степени (как у Mathematica и у нормализованного
               ; входа): иначе правила с образцом (/ 1 (* A B)) не видели вход (* A^-1 B^-1)
               (p (ac-build-prepared (nth r 2))))
          (hash-set! *rubi-prepared* id p)
          (rubi-prep-note t0)
          p))))

; RUBI.S8: файлы правил уже содержат переписанные имена (tools/rubi/generate.mjs, fixNames) —
; обход условия и правой части при первом применении (561 тыс. вызовов rubi-fix-names на задачу,
; до 3 с) не нужен. rubi-fix-names остаётся для правил, написанных вручную (применять к условию и правой части самому).
; RUBI.SYM.4: Log[E] в Mathematica вычисляется в 1 (ещё при чтении). Условия правил Rubi написаны с
; Log[F], где F — образец-переменная, и при F = E это единица: 4.7.7 #2 требует e^2+b^2 c^2 Log[F]^2 != 0,
; то есть при e = I, b = c = 1, F = E правило НЕ применимо. Порт оставлял (log E) символом: условие
; проходило, а ответ получал 0^-1 — так ∫exp x cosh x и ∫exp(asinh x) уходили в unknown вместо правила
; 6.7.7 #2 (F^(c(a+bx)) Cosh[d+e x]); см. REPORT-RUBI-SYM4.md. Правые части не трогаем: в них Log[E]
; сворачивает rubi-fold-log-e на готовом ответе.
; Свёртка подставляется В САМО УСЛОВИЕ (if вместо вызова функции): условие уходит в eval, и имя функции
; модуля там не разрешается — правило молча падало в try у rubi-cond-check («условие ложно»), интеграл
; уходил к следующей стратегии (∫sin^4 t·e^t в INT.HEUR № 17: 4 ошибки условий, ответ вместо Rubi дала
; подстановка tan(t/2)).
(define (rubi-log-wrap e)
  (cond ((not (pair? e)) e)
        ((equal? (car e) 'quote) e)
        ((and (equal? (car e) 'log) (= (length e) 2))
         (let ((a (rubi-log-wrap (cadr e))))
           (if (equal? a 'E) 1 (list 'if (list 'equal? a (list 'quote 'E)) 1 (list 'log a)))))
        (else (cons (car e) (map rubi-log-wrap (cdr e))))))
(define (rubi-fixed r)
  (let ((f (nth r 9)))
    (if f
        (begin (rubi-load-bodies f) (hash-ref *rubi-bodies* (nth r 1) #f))
        (cons (nth r 3) (nth r 4)))))

; Замена ?a -> a только для переменных образца; (quote ...) не трогается.
(define (rubi-strip-vars f alst)
  (cond ((symbol? f) (let ((p (assoc f alst))) (if p (cdr p) f)))
        ((pair? f)
         (if (equal? (car f) 'quote) f
             (cons (car f) (map (lambda (e) (rubi-strip-vars e alst)) (cdr f)))))
        (else f)))

; RUBI.13: дешёвые конъюнкты условия проверяются до полного тела. В условиях Rubi порядок
; конъюнктов исходный, и дорогие вычисления (деление многочленов, дифференцирование) могут стоять
; раньше дешёвых проверок вроде (rubi-integerq ?p) или (rubi-ltq (* ?p ?q) 0); предпроверка
; отсекает кандидата, не трогая порядок самого тела (оно считается как раньше, если прошла).
(define (rubi-form-size e)
  (if (pair? e)
      (let loop ((l (cdr e)) (n 1))
        (if (null? l) n (loop (cdr l) (+ n (rubi-form-size (car l))))))
      1))

; RUBI.S8: ответ по голове кэшируется (одни и те же головы повторяются в тысячах условий)
(define *rubi-exp-heads* (make-hash))
(define (rubi-expensive-head? h)
  (and (symbol? h)
       (let ((c (hash-ref *rubi-exp-heads* h 'none)))
         (if (equal? c 'none)
             (let* ((s (to-string h))
                    (v (or (string-contains? s "polynomial")
                           (string-contains? s "algebraic-function")
                           (string-contains? s "poly-q")
                           ; RUBI.SPEED: rubi-eqq/neq — это simplify+together (rubi-zero?), rubi-posq/negq —
                           ; TogetherSimplify и численная проверка знака; в условиях они стоят рядом с
                           ; дешёвыми freeq/integerq/ltq, и предпроверка дешёвых конъюнктов должна идти первой
                           (string-contains? s "eqq")
                           (string-contains? s "neq")
                           (string-contains? s "posq")
                           (string-contains? s "negq")
                           (string-contains? s "zero")
                           (string-contains? s "pseudo-binomial")
                           (string-contains? s "rational-function")
                           (string-contains? s "nice-sqrt")
                           (and (member? s '("diff" "simplify" "expand" "factor" "apart" "together" "solve")) #t))))
               (hash-set! *rubi-exp-heads* h v)
               v)
             c))))

; Ранний выход: после первой дорогой головы остальные не смотрим; без рекурсии по хвосту-атомам
(define (rubi-form-expensive? e)
  (and (pair? e)
       (or (rubi-expensive-head? (car e))
           (let loop ((l (cdr e)))
             (cond ((null? l) #f)
                   ((and (pair? (car l)) (rubi-form-expensive? (car l))) #t)
                   (else (loop (cdr l))))))))

(define (rubi-cheap-conjunct? e)
  (and (<= (rubi-form-size e) 10) (not (rubi-form-expensive? e))))

; конъюнкты верхнего уровня, вложенные and разворачиваются
(define (rubi-conjuncts e)
  (if (and (pair? e) (equal? (car e) 'and))
      (let flat ((l (cdr e)) (acc '()))
        (if (null? l) acc (flat (cdr l) (append acc (rubi-conjuncts (car l))))))
      (list e)))

; Замер одного вычисления условия правила: при выключенном профиле — прямой вызов без накладных.
; Лимит на одно условие (этап B): превышение считается ложью — тяжёлое условие
; (expand/poly-q на большом Px) иначе съедает сотни миллисекунд бюджета одной попытки.
; ВЫКЛЮЧЕН по умолчанию (#f): на Linux-раннере call-with-time-limit на каждом условии привёл к
; регрессии пилота (OK 46 % -> 15,6 %, 83 % таймаутов). Включать только после замера на стенде.
(define *rubi-cond-limit* #f)
(define *rubi-cond-timeouts* 0)
(define *rubi-cond-errors* 0)   ; сколько условий упало с ошибкой (диагностика)

(define (rubi-cond-check id f binds)
  (let* ((t0 (and *rubi-prof* (clock-us)))
         ; Ошибка вычисления условия (неподдержанная утилита, «Не число») = условие ложно для этих привязок.
         ; Перехват здесь, у места броска: исключение, прошедшее через весь стек сопоставителя (CPS,
         ; тысячи кадров), стоило ≈ 60 мс — по 10–15 таких условий на каждое подвыражение.
         (g (lambda ()
              (try (f binds)
                   (lambda (err)
                     (set! *rubi-cond-errors* (+ *rubi-cond-errors* 1))
                     (let ((m (string-append id " | cond | " (substring (to-string err) 0 (min 80 (string-length (to-string err)))))))
                       (hash-set! *rubi-errors* m (+ 1 (hash-ref *rubi-errors* m 0))))
                     #f))))
         (w (if *rubi-cond-limit*
                (call-with-time-limit *rubi-cond-limit* g)
                (list 'ok (g))))
         (v (if (and (pair? w) (equal? (car w) 'ok))
                (cadr w)
                (begin (set! *rubi-cond-timeouts* (+ *rubi-cond-timeouts* 1)) #f))))
    (if t0
        (let ((us (- (clock-us) t0)))
          (set! *rubi-p-cond* (+ *rubi-p-cond* us))
          (set! *rubi-cond-calls* (+ *rubi-cond-calls* 1))
          (set! *rubi-cond-slow*
                (take-n (insert-sorted (cons us id) *rubi-cond-slow*) *rubi-cond-slow-limit*))))
    v))

(define (insert-sorted x l)
  (cond ((null? l) (list x))
        ((> (car x) (car (car l))) (cons x l))
        (else (cons (car l) (insert-sorted x (cdr l))))))

(define (take-n l n)
  (if (or (null? l) (= n 0)) '() (cons (car l) (take-n (cdr l) (- n 1)))))

; RUBI.D2: журнал отказов для диагностики (tools/rubi/diagnose.mjs). Выключен (#f): в обычной работе цена -
; одна проверка флага на ложное условие и на шаг цикла. Записи (в *rubi-trace-log*, новые в голове):
;   (cond-fail id conj util expr)  - образец подошёл, условие ложно; conj - номер первого ложного конъюнкта (с 1),
;                                    util - первая утилита rubi:: в нём или #f; пишется только для тупикового expr
;   (rhs-fail id reason expr)      - правая часть не дала ответа (error/tainted/check/nested-unknown/no-rule/unknown)
;   (dead expr ncands nmatched)    - подвыражение, для которого перебраны все кандидаты и ни один не дал ответа
;   (seen expr)                    - нормализованное подвыражение дошло до цикла правил
;   (fire id expr depth binds)     - правило принято (ответ прошёл int-check) на expr на глубине depth (RUBI.FUZZ;
;                                    binds — привязки, с которыми сработало правило)
(define *rubi-trace* #f)
; RUBI.NORULE (диагностика, временно): id правила, чьи привязки печатаются в журнал ('binds id ne строкой).
(define *rubi-debug-binds* #f)
(define *rubi-trace-log* '())
(define *rubi-trace-ne* #f)                 ; выражение, для которого сейчас сопоставляется правило
(define *rubi-trace-cf* (make-hash))        ; expr -> (alist id -> (conj . util)): ложные условия при подошедшем образце
(define *rubi-trace-nc* (make-hash))        ; expr -> число кандидатов после отсева
(define *rubi-trace-conjs* (make-hash))     ; id -> список (util . замыкание конъюнкта)
(define *rubi-trace-err* #f)

(define (rubi-trace-add rec) (set! *rubi-trace-log* (cons rec *rubi-trace-log*)))

(define (rubi-trace-reset)
  (set! *rubi-trace-log* '())
  (set! *rubi-trace-ne* #f)
  (set! *rubi-trace-cf* (make-hash))
  (set! *rubi-trace-nc* (make-hash)))

; первая утилита rubi:: в конъюнкте (обход в глубину слева направо)
(define (rubi-trace-util c)
  (cond ((not (pair? c)) #f)
        ((and (symbol? (car c)) (string-contains? (to-string (car c)) "rubi::")) (car c))
        (else (let loop ((l (cdr c)))
                (cond ((null? l) #f)
                      ((rubi-trace-util (car l)) (rubi-trace-util (car l)))
                      (else (loop (cdr l))))))))

(define (rubi-trace-cond id cs alst binds)
  (let* ((fns (or (hash-ref *rubi-trace-conjs* id #f)
                  (let* ((bindings (map (lambda (v) (list (cdr (assoc v alst)) (list 'cadr (list 'assoc (list 'quote v) 'binds)))) (map car alst)))
                         (l (map (lambda (c)
                                   (cons (rubi-trace-util c)
                                         (eval (list 'lambda '(binds) (cons 'let (cons bindings (list (rubi-strip-vars c alst))))))))
                                 cs)))
                    (hash-set! *rubi-trace-conjs* id l)
                    l)))
         (hit (let loop ((l fns) (i 1))
                (cond ((null? l) (cons 0 #f))
                      ((not (try ((cdr (car l)) binds) (lambda (e) #f))) (cons i (car (car l))))
                      (else (loop (cdr l) (+ i 1))))))
         (tbl (hash-ref *rubi-trace-cf* *rubi-trace-ne* '()))
         (old (assoc id tbl)))
    ; из нескольких попыток одного правила на одном выражении - та, что дошла дальше
    (if (or (not old) (> (car hit) (cadr old)))
        (hash-set! *rubi-trace-cf* *rubi-trace-ne*
                   (cons (list id (car hit) (cdr hit)) (filter (lambda (p) (not (equal? (car p) id))) tbl))))))

; Компиляция условия правила в замыкание от привязок: на каждого кандидата больше нет
; ни ac-where-sub, ни eval — только let и вызов готовой лямбды.
; Условие правила из файла данных: замыкание-обёртка не читает тела, пока образец не подошёл
; (сопоставитель зовёт её только после структурного совпадения); без условия - #f, как раньше.
(define *rubi-cond-lazy* (make-hash))
(define (rubi-cond-fn r)
  (cond ((not (nth r 10)) #f)
        ((not (nth r 9)) (rubi-cond-fn-build r))
        (else
         (let ((id (nth r 1)))
           (or (hash-ref *rubi-cond-lazy* id #f)
               (let ((g (lambda (binds) ((rubi-cond-fn-build r) binds))))
                 (hash-set! *rubi-cond-lazy* id g)
                 g))))))

(define (rubi-cond-fn-build r)
  ; RUBI.SYM.4: Log[E] -> 1 в условии (автовычисление Mathematica, см. rubi-log-wrap)
  (let ((id (nth r 1)) (cd (rubi-log-wrap (car (rubi-fixed r)))))
    (if (null? cd)
        #f
        (or (hash-ref *rubi-cond-fns* id #f)
            (let* ((vars (caddr (rubi-prepared r)))
                   (alst (map (lambda (v)
                                (let ((s (to-string v)))
                                  (cons v (string->symbol (substring s 1 (string-length s))))))
                              vars))
                   (body0 (rubi-strip-vars cd alst))
                   (cs (rubi-conjuncts body0))
                   (cheap (filter rubi-cheap-conjunct? cs))
                   (body (if (or (null? cheap) (equal? (length cheap) (length cs)))
                             body0
                             (cons 'and (append cheap (filter (lambda (c) (not (rubi-cheap-conjunct? c))) cs)))))
                   (bindings (map (lambda (v)
                                    (list (cdr (assoc v alst))
                                          (list 'cadr (list 'assoc (list 'quote v) 'binds))))
                                  vars))
                   (t0 (and *rubi-prof* (clock-us)))
                   (f (eval (list 'lambda '(binds)
                                  (cons 'let (cons bindings (list body))))))
                   (_ (rubi-prep-note t0)))
              (let ((g (lambda (binds)
                         (let ((v (rubi-cond-check id f binds)))
                           (if (and *rubi-trace* (not v)) (rubi-trace-cond id cs alst binds))
                           v))))
                (hash-set! *rubi-cond-fns* id g)
                g))))))

(define (rubi-pvar? x)
  (and (symbol? x)
       (let* ((s (to-string x)) (n (string-length s)))
         (and (> n 0) (equal? (substring s 0 1) "?")))))

; Этап B, п.3: форма образца. Правило требует не меньше x-зависимых множителей, чем в образце
; конкретных (не голых `?u`) множителей, и содержит литеральные показатели (1/3, 3/2, 9/4 …),
; которых в выражении нет — тогда правило не совпадёт и его можно не перебирать.
(define *rubi-shape-index* #t)
; Диагностика: если это список — в него попадают все нормализованные выражения, дошедшие до rubi-int
; (проверка индекса на подвыражениях настоящих задач). В обычной работе #f.
(define *rubi-seen* #f)

(define (rubi-expr-xfactors e x)
  (cond ((not (contains-sym? e x)) 0)
        ((and (pair? e) (equal? (car e) '*))
         (let loop ((fs (cdr e)) (n 0))
           (if (null? fs)
               n
               (loop (cdr fs) (if (contains-sym? (car fs) x) (+ n 1) n)))))
        (else 1)))

(define (rubi-pat-min-factors pat)
  (if (and (pair? pat) (equal? (car pat) '*))
      (let loop ((fs (cdr pat)) (n 0))
        (if (null? fs)
            n
            (loop (cdr fs) (if (rubi-pvar? (car fs)) n (+ n 1)))))
      0))

(define (rubi-expr-exponents e acc)
  (if (pair? e)
      (let ((acc (if (and (equal? (car e) '^) (= (length (cdr e)) 2) (number? (nth e 2)))
                     (cons (nth e 2) acc)
                     acc)))
        (let loop ((l (cdr e)) (a acc))
          (if (null? l) a (loop (cdr l) (rubi-expr-exponents (car l) a)))))
      acc))

(define (rubi-pat-exponents p acc)
  (if (pair? p)
      (let* ((h (car p))
             (literal (and (symbol? h) (not (rubi-pvar? h))))
             (acc (if (and literal (equal? h '^) (= (length (cdr p)) 2) (number? (nth p 2)))
                      (cons (nth p 2) acc)
                      acc)))
        (let loop ((l (cdr p)) (a acc))
          (if (null? l) a (loop (cdr l) (rubi-pat-exponents (car l) a)))))
      acc))

(define *rubi-exps-sign* #t)   ; RUBI.CH4: диагностика — #f выключает приём показателя с обратным знаком
(define (rubi-exps-subset? need have)
  (let loop ((l need))
    (cond ((null? l) #t)
          ; RUBI.CH4: показатель образца может стоять у выражения обратной степенью (Sec[x]^n -> Cos[x]^-n,
          ; см. ac-trig-reciprocal-of): принимаем и противоположный знак
          ((and *rubi-exps-sign* (number? (car l)) (not (= (car l) 0))
                (or (member? (car l) have) (member? (- 0 (car l)) have)))
           (loop (cdr l)))
          ((member? (car l) have) (loop (cdr l)))
          (else #f))))

; Правило r (элемент *rubi-rules*) допускается формой выражения: xc — число x-зависимых множителей
; верхнего уровня, exps — числовые показатели степеней выражения.
(define (rubi-shape-ok? r xc exps)
  (or (not *rubi-shape-index*)
      (and (>= xc (nth r 7)) (rubi-exps-subset? (nth r 8) exps))))

; Диагностика корректности индекса: правила, которые индекс по форме отсёк, хотя по головам
; они проходили, но образец структурно подходит к выражению (условие не проверяется — это
; надмножество настоящих совпадений). Пусто — индекс ничего не потерял. Обязательные головы
; здесь не проверяются повторно: берутся правила из rubi-candidates, то есть уже отобранные.
(define (rubi-shape-lost e x)
  (set! *rubi-cands* (make-hash))
  (let* ((ne (ac-strip-units (ac-norm (if (rubi-sqrt-head? e) (rubi-normalize-heads e) e))))
         (heads (rubi-expr-heads ne '()))
         (xc (rubi-expr-xfactors ne x))
         (exps (rubi-expr-exponents ne '())))
    (filter (lambda (r)
              (and (rubi-prefilter? (nth r 6) heads)
                   (not (rubi-shape-ok? r xc exps))
                   (let ((b (try (ac-match-prepared (rubi-prepared r) ne #f) (lambda (err) #f))))
                     (and b #t))))
            (rubi-candidates ne heads))))

(define (rubi-head-key pat)
  (if (and (pair? pat) (symbol? (car pat)) (not (rubi-pvar? (car pat))))
      (car pat)
      '*))

; RUBI.MATCH: необязательное слагаемое (a_. в сумме) может отсутствовать, поэтому голова + обязательна только
; тогда, когда обязательных слагаемых не меньше двух: иначе сумма может выродиться в одно слагаемое (или в 0),
; и требовать + у выражения нельзя — (sin (+ c_. (* d_. x))) с c=0 подходит к sin(x), где головы + нет.
(define (rubi-pat-mandatory-sums items)
  (length (filter (lambda (it) (not (and (ac-pattern-var? it) (ac-opt-var? it)))) items)))

(define (rubi-pat-heads p acc)
  (cond ((symbol? p) acc)
        ((pair? p)
         (let* ((h (car p))
                (need (and (symbol? h) (not (rubi-pvar? h))
                           (not (member? h '(* ^ / -)))
                           (or (not (equal? h '+)) (>= (rubi-pat-mandatory-sums (cdr p)) 2))))
                (acc (if need (cons h acc) acc)))
           (rubi-pat-heads-list (cdr p) acc)))
        (else acc)))

(define (rubi-pat-heads-list l acc)
  (if (null? l) acc (rubi-pat-heads-list (cdr l) (rubi-pat-heads (car l) acc))))

(define (rubi-expr-heads e acc)
  (if (pair? e)
      (let* ((acc (if (symbol? (car e)) (cons (car e) acc) acc))
             (al (rubi-head-alias (car e))))
        (rubi-expr-heads-list (cdr e) (if al (append al acc) acc)))
      acc))

; RUBI.CH4: образцы Rubi написаны в csc/cot/sec (905/528/400 вхождений), а нормализованное выражение — через
; sin/tan/cos (упрощатель порта: Csc[x] -> 1/Sin[x], Cot[x] -> 1/Tan[x], Sec[x] -> 1/Cos[x]; сопоставитель
; сводит головы образца к степеням, см. ac-trig-reciprocal-of в match.lisp). Обязательная голова csc/cot/sec
; считается выполненной, если в выражении есть соответствующая прямая голова. Фильтр только ослабляется
; (кандидатов больше), на корректность не влияет.
(define (rubi-head-alias h)
  (cond ((equal? h 'sin) '(sin csc))
        ((equal? h 'tan) '(tan cot))
        ((equal? h 'cos) '(cos sec))
        (else #f)))

(define (rubi-expr-heads-list l acc)
  (if (null? l) acc (rubi-expr-heads-list (cdr l) (rubi-expr-heads (car l) acc))))

(define (rubi-prefilter? req heads)
  (every? (lambda (h) (member? h heads)) req))

; RUBI.SPEED: класс корня образца — дешёвый (O(1)) отсев кандидата до полного AC-поиска.
; Сопоставитель ac-mt проверяет корень образца первым узлом, поэтому несовпадение класса корня
; означает «правило не подойдёт» без всякого перебора; при 900+ кандидатах на выражение это
; основная доля фазы сопоставления. Классы (консервативные: сомнительный случай — 'any):
;   'any          — корень-переменная, константа с переменными, (^ ...) (единица степени), AC-узел из
;                  одного фиксированного аргумента, узел с головой-переменной;
;   ('head h n)   — узел (h ...) ровно с n аргументами;
;   ('ac op plain)— AC-узел +/* с ≥2 фиксированными: выражение должно быть узлом той же операции,
;                  кроме случая, когда фиксированный аргумент-переменная может получить нейтральный элемент;
;   'pair         — голова-переменная (F_[...]) требует пары.
(define (rubi-pat-root-key pat)
  (cond ((symbol? pat)
         (if (ac-pattern-var? pat) 'any (list 'const pat)))
        ((not (pair? pat)) (list 'const pat))
        (else
         (let ((h (car pat)) (n (- (length pat) 1)))
           (cond ((ac-pattern-var? h) 'pair)
                 ((and (or (equal? h '+) (equal? h '*)) (>= n 2))
                  (let ((plain (length (filter ac-pattern-var? (cdr pat)))))
                    (if (>= plain 1) 'any (list 'ac h))))
                 ((and (or (equal? h '+) (equal? h '*)) (= n 1)) 'any)
                 ((equal? h '^) 'any)
                 (else (list 'head h n)))))))

(define *rubi-root-keys* (make-hash))
(define *rubi-root-filter* #t)   ; диагностика: #f — фильтр по классу корня выключен (сравнение до/после)
(define (rubi-rule-root-key r)
  (hash-ref *rubi-root-keys* (nth r 1) 'any))

; (rubi-root-ok? класс выражение): #f — правило заведомо не подойдёт (ни один AC-вариант не начнётся)
(define (rubi-root-ok? k e)
  (if (not *rubi-root-filter*)
      #t
      (cond ((equal? k 'any) #t)
        ((equal? k 'pair) (pair? e))
        ((equal? (car k) 'head)
         (and (pair? e) (equal? (car e) (cadr k)) (= (caddr k) (length (cdr e)))))
        ((equal? (car k) 'ac) (and (pair? e) (equal? (car e) (cadr k))))
        ((equal? (car k) 'const) (equal? (cadr k) e))
        (else #t))))

; Диагностика корректности фильтра по классу корня: при *rubi-root-check* отсеянное правило
; проверяется полным сопоставлением, и найденное совпадение попадает в *rubi-root-bad* (правило
; возвращается в перебор, чтобы поведение не менялось).
(define *rubi-root-check* #f)
(define *rubi-root-bad* '())
(define (rubi-root-suspect? r ne)
  (and *rubi-root-check*
       (let ((b (try (ac-match-prepared (rubi-prepared r) ne (rubi-cond-fn r)) (lambda (err) 'err))))
         (if (and b (not (equal? b 'err)))
             (begin (set! *rubi-root-bad* (cons (list (nth r 1) (rubi-rule-root-key r) ne) *rubi-root-bad*))
                    #t)
             #f))))

; RUBI.S8: то же по хеш-множеству голов (одно на выражение, а не member? по списку на каждое правило)
(define (rubi-head-set heads)
  (let ((h (make-hash)))
    (for-each (lambda (k) (hash-set! h k #t)) heads)
    h))

(define (rubi-prefilter-set? req hs)
  (let loop ((l req))
    (cond ((null? l) #t)
          ((hash-ref hs (car l) #f) (loop (cdr l)))
          (else #f))))

(define (rubi-unique l acc)
  (cond ((null? l) (reverse acc))
        ((member? (car l) acc) (rubi-unique (cdr l) acc))
        (else (rubi-unique (cdr l) (cons (car l) acc)))))

(define (rubi-bucket k) (hash-ref *rubi-hindex* k '()))

; списки правил в корзинах идут по убыванию номера порядка (cons при сборке индекса);
; слияние итеративное — рекурсия на 7.5 тыс. правил давала переполнение стека.
(define (rubi-merge2 a b)
  (let loop ((a a) (b b) (acc '()))
    (cond ((null? a) (append (reverse acc) b))
          ((null? b) (append (reverse acc) a))
          ((> (car (car a)) (car (car b))) (loop (cdr a) b (cons (car a) acc)))
          (else (loop a (cdr b) (cons (car b) acc))))))

(define (rubi-merge-lists ls)
  (cond ((null? ls) '())
        ((null? (cdr ls)) (car ls))
        (else (rubi-merge-lists (cons (rubi-merge2 (car ls) (cadr ls)) (cddr ls))))))

; Кандидаты — объединение корзин по головам, которые требует образец: правило с непустым
; набором обязательных голов может подойти, только если все они есть в выражении (rubi-prefilter?).
; Правила без таких голов (чистая алгебра) лежат в корзине none и перебираются всегда.
(define (rubi-candidates e heads)
  (or (hash-ref *rubi-cands* e #f)
      (let* ((hs (rubi-unique heads '()))
             (ls (cons (rubi-bucket 'none) (map rubi-bucket hs)))
             (ls (filter (lambda (l) (not (null? l))) ls))
             (v (reverse (rubi-merge-lists ls))))
        (hash-set! *rubi-cands* e v)
        v)))

; RUBI.INDEX: дерево признаков образца и отсев кандидатов по нему.
; Совпадение с правилом возможно, только если в выражении есть все структурные признаки образца:
;   (*node* путь голова арность) — узел с этой головой и арностью на этом пути;
;   (*ac* путь операция)        — узел +/* на этом пути (образец с двумя и более не-переменными аргументами
;                                одиночному аргументу не подходит: ac-mt-ac, ac-fixed);
;   (*pow* путь)                — степень на этом пути; (*pow* путь показатель) — степень с этим показателем;
;   (*any* голова арность)      — узел с этой головой и арностью где угодно.
; Путь — список шагов от корня: голова узла, операция AC-узла, ^ для степени. Порядок аргументов AC-узла в путь
; не входит и дети перебираются как мультимножество — коммутативность и ассоциативность + и * учтены по
; построению (как DiscrTree Mathlib / MatchPy). Переменная образца — джокер: признаков не даёт.
; Признаки консервативные. Если образец может совпасть с выражением другой формы — необязательный показатель
; степени (^ ?u ?n. годится и не-степени), единственный не-переменный аргумент суммы/произведения (узел может
; выродиться в этот аргумент), голова-переменная F_[...], постоянное поддерево (компилируется в K через
; simplify) — путь ниже этого узла недостоверен, и оттуда выдаются только беспутевые признаки (*any*).
; Ложных отсечений быть не должно: проверка — rubi-index-lost (rubi-index-check) и тесты rubi-index.lisp.
(define *rubi-index* #t)            ; флаг для замера: #f — перебор как до RUBI.INDEX
(define *rubi-feats* (make-hash))   ; id правила → список признаков
(define *rubi-p-idxn* 0)            ; профиль: сколько кандидатов отсеял индекс
(define *rubi-index-check* #f)      ; диагностика: каждый отсеянный кандидат проверяется полным сопоставлением
(define *rubi-index-bad* '())       ; найденные ложные отсечения: (id выражение)

; переменная образца в поддереве (ac-has-var? не экспортируется из match)
(define (rubi-pat-has-var? p)
  (cond ((symbol? p) (ac-pattern-var? p))
        ((pair? p) (any? rubi-pat-has-var? (cdr p)))
        (else #f)))

(define (rubi-pat-rigid? a)
  ; не-переменный аргумент AC-узла: обязателен и структурен. Необязательная (?a.) и сегментная (?r...) могут
  ; отсутствовать; обычная переменная под + и * тоже (OneIdentity: ac-skippable? при явной разметке).
  (not (and (symbol? a) (ac-pattern-var? a))))

; узел жёсткой головы: признак с путём — только при достоверном пути
(define (rubi-feat-node path h n certain? acc)
  (let ((acc (cons (list '*any* h n) acc)))
    (if certain? (cons (list '*node* path h n) acc) acc)))

(define (rubi-pat-feats* p path certain? acc)
  (cond
    ((or (symbol? p) (not (pair? p)))
     (if (and (symbol? p) (ac-pattern-var? p))
         acc
         (rubi-feat-node path p 0 certain? acc)))
    ; постоянное поддерево компилируется в K и сравнивается целиком после simplify — структуру не гарантируем
    ((not (rubi-pat-has-var? p)) acc)
    (else
     (let ((h (car p)) (args (cdr p)))
       (cond
         ; голова-переменная F_[...]: голова любая, путь недостоверен
         ((and (symbol? h) (ac-pattern-var? h)) (rubi-pat-feats-any args acc))
         ((or (equal? h '+) (equal? h '*))
          (let* ((rigid (filter rubi-pat-rigid? args))
                 (node? (and certain? (>= (length rigid) 2))))
            (rubi-pat-feats-list rigid (cons h path) node?
                                 (if node? (cons (list '*ac* path h) acc) acc))))
         ((equal? h '^)
          (if (not (= (length args) 2))
              (rubi-pat-feats-any args acc)
              (let ((base (car args)) (ex (cadr args)))
                ; (^ ?u ?n.): показатель необязателен — образец годится и не-степени (единица степени)
                (let ((cert (and certain? (not (and (symbol? ex) (ac-pattern-var? ex) (ac-opt-var? ex))))))
                  (let ((acc1 (if cert (cons (list '*pow* path) acc) acc)))
                    (let ((acc2 (if (and cert (number? ex)) (cons (list '*pow* path ex) acc1) acc1)))
                      ; показатель идёт тем же шагом ^, что и основание: его путь неразличим — только беспутевые признаки
                      (rubi-pat-feats* ex (cons '^ path) #f
                                       (rubi-pat-feats* base (cons '^ path) cert acc2))))))))
         (else
          (rubi-pat-feats-list args (cons h path) certain?
                               (rubi-feat-node path h (length args) certain? acc))))))))

(define (rubi-pat-feats-list l path certain? acc)
  (if (null? l) acc (rubi-pat-feats-list (cdr l) path certain? (rubi-pat-feats* (car l) path certain? acc))))

; аргументы узла с недостоверным путём: только беспутевые признаки
(define (rubi-pat-feats-any l acc)
  (if (null? l) acc (rubi-pat-feats-any (cdr l) (rubi-pat-feats* (car l) '() #f acc))))

(define (rubi-pat-feats p) (rubi-pat-feats* p '() #t '()))

; Признаки выражения — набор всего, что в нём есть; путь каждого узла известен точно.
(define (rubi-expr-feats* e path fh)
  (cond
    ((or (symbol? e) (not (pair? e)))
     (hash-set! fh (list '*node* path e 0) #t)
     (hash-set! fh (list '*any* e 0) #t)
     fh)
    (else
     (let ((h (car e)) (args (cdr e)))
       (cond
         ((or (equal? h '+) (equal? h '*))
          (hash-set! fh (list '*ac* path h) #t)
          (rubi-expr-feats-list args (cons h path) fh))
         ((and (equal? h '^) (= (length args) 2))
          (hash-set! fh (list '*pow* path) #t)
          (if (number? (cadr args)) (hash-set! fh (list '*pow* path (cadr args)) #t))
          (rubi-expr-feats-list args (cons '^ path) fh))
         (else
          (hash-set! fh (list '*node* path h (length args)) #t)
          (hash-set! fh (list '*any* h (length args)) #t)
          (rubi-expr-feats-list args (cons h path) fh)))))))

(define (rubi-expr-feats-list l path fh)
  (if (null? l) fh (rubi-expr-feats-list (cdr l) path (rubi-expr-feats* (car l) path fh))))

(define (rubi-expr-feats e)
  (rubi-expr-feats* e '() (make-hash)))

(define (rubi-rule-feats r) (hash-ref *rubi-feats* (nth r 1) '()))

; все признаки образца должны быть в выражении; пустой набор (голые переменные) проходит всегда
(define (rubi-feats-ok? r fh)
  (or (not *rubi-index*)
      (every? (lambda (a) (hash-ref fh a #f)) (rubi-rule-feats r))))

; Диагностика корректности индекса (как rubi-shape-lost): правила, отсеянные индексом, но совпадающие с
; выражением (условие правила не проверяется — это надмножество настоящих совпадений).
; Пусто — индекс ничего не потерял.
(define (rubi-index-lost e)
  (set! *rubi-cands* (make-hash))
  (let ((fh (rubi-expr-feats e)))
    (filter (lambda (r)
              (and (not (rubi-feats-ok? r fh))
                   (let ((b (try (ac-match-prepared (rubi-prepared r) e #f) (lambda (err) #f))))
                     (and b #t))))
            (rubi-candidates e (rubi-expr-heads e '())))))

; Под *rubi-index-check* отсеянный кандидат проверяется полным сопоставлением: найденное совпадение — ложное
; отсечение (правило возвращается в перебор, поведение не меняется).
(define (rubi-index-suspect? r ne fh)
  (and *rubi-index-check*
       (let ((b (try (ac-match-prepared (rubi-prepared r) ne (rubi-cond-fn r)) (lambda (err) 'err))))
         (if (and b (not (equal? b 'err)))
             (begin (set! *rubi-index-bad* (cons (list (nth r 1) ne) *rubi-index-bad*)) #t)
             #f))))

(define (rubi-build-index)
  (set! *rubi-hindex* (make-hash))
  (set! *rubi-prepared* (make-hash))
  (set! *rubi-fixed* (make-hash))
  (set! *rubi-cond-fns* (make-hash))
  (set! *rubi-root-keys* (make-hash))
  (set! *rubi-feats* (make-hash))
  (for-each (lambda (r)
              ; класс корня и признаки — по нормализованному образцу (rubi-pat-normalize: под единой формой —
              ; rubi-nf, без флага — ac-norm/ac-strip-units, как в ac-build-prepared); нормализация одна на оба индекса.
              (let ((np (if *rubi-nf*
                            ; RUBI.GEN.2: под #t образец пришёл нормализованным (rubi-rules-nf-data) — rubi-nf не нужен
                            (nth r 2)
                            (ac-strip-units (ac-norm (nth r 2))))))
                (hash-set! *rubi-root-keys* (nth r 1) (rubi-pat-root-key np))
                (hash-set! *rubi-feats* (nth r 1) (rubi-pat-feats np)))
              (let ((hs (rubi-unique (nth r 6) '())))
                (if (null? hs)
                    (hash-set! *rubi-hindex* 'none (cons r (rubi-bucket 'none)))
                    (for-each (lambda (h)
                                (hash-set! *rubi-hindex* h (cons r (rubi-bucket h))))
                              hs))))
            *rubi-rules*))

(define (rubi-rules-loaded?) *rubi-loaded*)

; Двухступенчатая загрузка. Полная загрузка 199 файлов (5 МБ) занимает 4–6 с и на стенде (таймаут задачи
; 5 с) первая же задача убивалась, процесс перезапускался, и всё повторялось: пилот 6d19a5f дал 83 %
; таймаутов. Глава 1 (алгебра, 67 файлов, 2 МБ) — префикс общего порядка правил, ей хватает ≈1,7 с.
; RUBI.DET: двухступенчатость снята - rubi-ensure грузит все главы (иначе ответ зависел от истории процесса);
; rubi-ensure-full[-until] остались как заглушки (при stage 2 - #t).
(define *rubi-stage* 0)   ; 0 — правила заданы вручную (тесты), 1 — только глава 1, 2 — всё

(define (rubi-stage1-file? f)
  (and (> (string-length f) 2) (equal? (substring f 0 2) "1.")))

; RUBI.CH: утилиты, нужные только своим главам, живут в lib/rubi/utils-<буква>.lisp:
; a — 1.1.2–1.1.4, b — 1.2–1.4, c — 4, d — 2–3. Файл грузится перед правилами своей главы один раз; отсутствующий файл —
; не ошибка (глава ещё без своих утилит), любая другая ошибка загрузки — пробрасывается.
(define rubi-chapter-utils
  '(("1.1.2" "a") ("1.1.3" "a") ("1.1.4" "a") ("1.2" "b") ("1.3" "b") ("1.4" "b") ("4." "c") ("2." "d") ("3." "d")))
(define *rubi-chapter-utils-loaded* '())
(define (rubi-chapter-letter f)
  (let loop ((l rubi-chapter-utils))
    (cond ((null? l) #f)
          ((let ((p (car (car l))))
             (and (>= (string-length f) (string-length p)) (equal? (substring f 0 (string-length p)) p)))
           (cadr (car l)))
          (else (loop (cdr l))))))
(define (rubi-load-chapter-utils files)
  (for-each
   (lambda (f)
     (let ((c (rubi-chapter-letter f)))
       (if (and c (not (member? c *rubi-chapter-utils-loaded*)))
           (begin
             (set! *rubi-chapter-utils-loaded* (cons c *rubi-chapter-utils-loaded*))
             (try (load (string-append lib-dir "rubi/utils-" c ".lisp"))
                  (lambda (e)
                    (if (string-contains? (to-string e) "файл не найден") #f (error (to-string e)))))))))
   files))

(define (rubi-load-files files)
  ; *rubi-rules* хранится по возрастанию порядка; add-rule добавляет в голову — разворачиваем туда и обратно
  (rubi-load-chapter-utils files)
  (set! *rubi-rules* (reverse *rubi-rules*))
  ; RUBI.GEN.2: под #t образцы заменяются предвычисленными для единой формы — нормализации нет
  ; RUBI.GEN.3: отличия копятся во время цикла (каждый .nf.lisp добавляет свои записи) и применяются ОДНИМ
  ; проходом после загрузки всех файлов. Применять до цикла бессмысленно: там список ещё пуст.
  (set! *rubi-nf-overrides* '())
  (for-each (lambda (f)
              (load (string-append lib-dir "rubi/rules/" f ".lisp"))
              (if *rubi-nf* (rubi-load-nf-file f)))
            files)
  (rubi-apply-nf-overrides)
  (if (and *rubi-nf* *rubi-trig-nf*) (rubi-renf-rules))
  (set! *rubi-rules* (reverse *rubi-rules*))
  (rubi-build-index))

; RUBI.TRIG: образцы единой формы приводятся к форме ядра (tan/sec/csc/cot -> sin/cos, см. nf.lisp) ПРИ ЗАГРУЗКЕ:
; предвычисленные .nf.lisp хранят их с головами sec/tan. rubi-nf идемпотентна на готовой форме.
(define (rubi-renf-rules)
  (set! *rubi-rules*
        (map (lambda (r)
               (let ((p (nth r 2)))
                 (if (rubi-pat-trig-head? p)
                     (let ((pn (rubi-nf p)))
                       (list (nth r 0) (nth r 1) pn (nth r 3) (nth r 4) (nth r 5)
                             (rubi-pat-heads pn '()) (rubi-pat-min-factors pn) (rubi-pat-exponents pn '())
                             (nth r 9) (nth r 10)))
                     r)))
             *rubi-rules*)))
(define (rubi-pat-trig-head? p)
  (cond ((not (pair? p)) #f)
        ((equal? (car p) 'quote) #f)
        ((and (member? (car p) '(sec csc tan cot)) (pair? (cdr p))) #t)
        (else (any? rubi-pat-trig-head? (cdr p)))))

; RUBI.SYM.3: смена формы (*rubi-nf*) должна применяться ДО загрузки правил и до построения индекса.
; Причина: rubi-build-index (и ac-build-prepared) нормализуют образцы и признаки через *rubi-nf* и
; ac-norm, а ac-norm читает флаг match::*ac-trig-recip* — он выставлялся только в rubi-integrate*,
; то есть ПОСЛЕ rubi-ensure. В результате первый вызов в процессе (он же загружает правила) строил
; индекс в чужой форме, и задача, требующая шлюза DeactivateTrig (∫sinh x, ∫cosh(a+bx)), получала
; unknown; второй вызов работал. Эталон (symbolica-integrate) форму не переключает — у него правила
; собраны заранее под одну форму, поэтому в порте переключение обязано пересобрать производные кэши.
(define *rubi-form* 'unset)
; RUBI.GEN.2: состояние формы (правила, порядок и пакет индекса) кэшируется: переключение флага в процессе
; (тесты, A/B) не нормализует и не индексирует 8506 образцов заново — повторный выбор формы это только
; перестановка указателей. Новая форма читается из файлов один раз (базовые данные + <файл>.nf.lisp).
(define *rubi-forms* (make-hash))   ; форма -> (правила порядок hindex prepared fixed cond-fns root-keys feats)
(define (rubi-state-save)
  (hash-set! *rubi-forms* *rubi-form*
             (list *rubi-rules* *rubi-ord* *rubi-hindex* *rubi-prepared* *rubi-fixed*
                   *rubi-cond-fns* *rubi-root-keys* *rubi-feats*)))
(define (rubi-state-restore st)
  (set! *rubi-rules* (nth st 0))
  (set! *rubi-ord* (nth st 1))
  (set! *rubi-hindex* (nth st 2))
  (set! *rubi-prepared* (nth st 3))
  (set! *rubi-fixed* (nth st 4))
  (set! *rubi-cond-fns* (nth st 5))
  (set! *rubi-root-keys* (nth st 6))
  (set! *rubi-feats* (nth st 7)))
(define (rubi-form-sync)
  (if (equal? *rubi-form* *rubi-nf*)
      #f
      (begin
        (if *rubi-loaded* (rubi-state-save))
        (set! *rubi-form* *rubi-nf*)
        (ac-trig-recip! (not *rubi-nf*))
        (set! *rubi-cands2* (make-hash))
        (set! rubi::*rubi-deact-cache* (make-hash))
        ; RUBI.SYM.4: prepared-образцы таблицы Unify (inert.lisp) тоже зависят от формы: их нормализует
        ; ac-norm (см. ключ в rubi-inert-prepared). Пересборка вместе с индексом держит кэш в одной форме
        ; и не даёт ему расти на две формы сразу.
        (set! *rubi-inert-prep* (make-hash))
        (if *rubi-loaded*
            (let ((st (hash-ref *rubi-forms* *rubi-form* #f)))
              (cond
                (st (rubi-state-restore st))
                ; RUBI.GEN.3: порядок файлов не загружен (order.lisp не читался) — правила заданы кодом
                ; (rubi-test-setup/rubi-real-setup в тестах). Перечитывать нечего: rubi-rule-files пуст,
                ; и перезагрузка молча теряла набор правил (rubi/11: integrate → unknown). Оставляем
                ; правила как есть и только пересобираем индекс в новой форме.
                ((null? rubi-rule-files) (rubi-build-index))
                (else
                 ; формы ещё нет в кэше: перечитываем данные в новой форме
                 (let ((manual (filter (lambda (r) (not (nth r 9))) *rubi-rules*)))
                   (set! *rubi-rules* '())
                   (set! *rubi-ord* 0)
                   (rubi-load-files rubi-rule-files)
                   ; правила, добавленные кодом (тесты) до переключения, переживают перезагрузку
                   (if (pair? manual)
                       (begin (set! *rubi-rules* (append *rubi-rules* manual))
                              (set! *rubi-ord* (+ *rubi-ord* (length manual)))
                              (rubi-build-index))))))))
        #t)))

(define (rubi-ensure)
  (if *rubi-loaded*
      #t
      (begin
        (load (string-append lib-dir "rubi/rules/order.lisp"))
        ; RUBI.DET: набор правил не зависит от входа и истории процесса - всегда загружаются все главы
        (rubi-load-files rubi-rule-files)
        (set! *rubi-stage* 2)
        (set! *rubi-loaded* #t)
        #t)))

(define (rubi-ensure-full)
  (rubi-ensure-full-until #f))

; RUBI.S16: полная загрузка (≈ 4,3 с на стенде) не помещается в 5 с задачи: процесс убивался, а следующая
; задача снова платила холодный старт. Теперь догрузка идёт по файлам и останавливается, когда часы
; (clock-us) дошли до until (#f - без предела); недогруженное доделывает следующий вызов, индекс
; перестраивается один раз в конце. Результат: #t - загружено всё, #f - вызывающий возвращает unknown.
(define *rubi-pending-files* #f)
(define (rubi-ensure-full-until until)
  (if (not (equal? *rubi-stage* 1))
      #t
      (begin
        (if (not *rubi-pending-files*)
            (set! *rubi-pending-files* (filter (lambda (f) (not (rubi-stage1-file? f))) rubi-rule-files)))
        (set! *rubi-rules* (reverse *rubi-rules*))
        (let loop ()
          (if (and (pair? *rubi-pending-files*) (or (not until) (< (clock-us) until)))
              (begin
                (rubi-load-chapter-utils (list (car *rubi-pending-files*)))
                (load (string-append lib-dir "rubi/rules/" (car *rubi-pending-files*) ".lisp"))
                (set! *rubi-pending-files* (cdr *rubi-pending-files*))
                (loop))))
        (set! *rubi-rules* (reverse *rubi-rules*))
        (if (null? *rubi-pending-files*)
            (begin (rubi-build-index)
                   (set! *rubi-stage* 2)
                   #t)
            #f))))

; вход целиком из алгебраических операций (глава 1 правил достаточна); подвыражения без x - константы
; (exp(2), pi) и голов не требуют: ∫pi/sqrt(16 - exp(2)) не должен грузить остальные главы (4,3 с)
(define (rubi-algebraic? e)
  (cond ((not (pair? e)) #t)
        ((member? (car e) '(+ * ^ / - sqrt)) (every? rubi-algebraic? (cdr e)))
        (else #f)))
(define (rubi-algebraic-in? e x)
  (cond ((not (pair? e)) #t)
        ((not (contains-sym? e x)) #t)
        ((member? (car e) '(+ * ^ / - sqrt)) (every? (lambda (a) (rubi-algebraic-in? a x)) (cdr e)))
        (else #f)))

(define (rubi-bind-pair b)
  (let* ((s (to-string (car b))) (n (string-length s)))
    (list (string->symbol (substring s 1 n))
          (list 'quote (cadr b)))))

; профиль: собственное время правых частей по правилам (за вычетом вложенных вычислений)
(define *rubi-eval-by-id* (make-hash))
(define *rubi-cur-id* #f)
(define *rubi-last-dt* 0)
; Sqrt[число] в правой части: встроенный sqrt даёт алгебраическое число root(...), которое не печатается радикалом
; и не вычисляется оракулом; Rubi держит Sqrt[3] как 3^(1/2) - так и здесь.
(define (rubi-num-sqrt u) (if (number? u) (simplify (list '^ u 1/2)) (sqrt u)))
; RUBI.CH3.2: E в правой части записан генератором как (exp 1), а встроенный exp от числа даёт ПЛАВАЮЩЕЕ 2.718...:
; подзадача получала основание (^ 2.718 ...) вместо (^ E ...), правила 2.x с F^(c (a+b x)) к ней не применялись
; (3.1.2 #10: x^m (a+b log(c x^n))^p -> exp(..)(a+b x)^p падала на каждом таком интеграле). E остаётся символом E,
; как во входе (rubi-normalize-heads); E^(рациональное) — тоже символьно.
(define (rubi-num-exp u)
  (cond ((equal? u 1) 'E)
        ((and (number? u) (or (integer? u) (equal? (type-of u) 'rational))) (list '^ 'E u))
        (else (exp u))))
; Log[2] в правой части: встроенный log от точного числа даёт ПЛАВАЮЩЕЕ 0.693… (ответ ∫log(2+x³)/x содержал 0.6931471805599453);
; Mathematica держит Log[2] символом — как и здесь: log точного числа остаётся (log n), log 1 = 0.
(define (rubi-num-log u)
  (cond ((equal? u 1) 0)
        ((and (number? u) (or (integer? u) (equal? (type-of u) 'rational)) (> u 0)) (list 'log u))
        (else (log u))))
(define (rubi-eval-binds binds)
  (cons (list 'sqrt (list 'quote rubi-num-sqrt))
        (cons (list 'exp (list 'quote rubi-num-exp))
              (cons (list 'log (list 'quote rubi-num-log)) (map rubi-bind-pair binds)))))
;; RUBI.CH3: условия, записанные simplify при вычислении правой части кандидата (2F1 при z = 1 и т. п.), не условия ответа
(define (rubi-eval-quiet binds rhs)
  (car (capture-conditions (lambda () (eval (list (quote let) (rubi-eval-binds binds) rhs))))))
(define (rubi-eval rhs binds)
  (if (not *rubi-prof*)
      (rubi-eval-quiet binds rhs)
      (let* ((c0 *rubi-p-eval-sum*)
             (id *rubi-cur-id*)
             (acc0 *rubi-p-int-acc*)
             (_a (set! *rubi-p-int-acc* 0))
             (t0 (clock-us))
             (v (rubi-eval-quiet binds rhs))
             (dt (- (clock-us) t0))
             (_b (begin (set! *rubi-p-rhs* (+ *rubi-p-rhs* (- dt *rubi-p-int-acc*)))
                        (set! *rubi-p-int-acc* acc0)))
             (nested (- *rubi-p-eval-sum* c0)))
        (hash-set! *rubi-eval-by-id* id (+ (hash-ref *rubi-eval-by-id* id 0) (- dt nested)))
        (set! *rubi-last-dt* dt)
        (set! *rubi-p-eval-self* (+ *rubi-p-eval-self* (- dt nested)))
        (set! *rubi-p-eval-sum* (+ *rubi-p-eval-sum* dt))
        v)))

; Отказ с причиной: причина идёт в журнал (гистограмма — в профиле), результат просто unknown.
(define (rubi-fail why)
  (set! *rubi-last-reason* why)
  (rubi-note-reason why)
  'unknown)

; свежий символ base1, base2, ... которого нет в выражении
(define (rubi-fresh-sym e base)
  (let loop ((i 1))
    (let ((s (string->symbol (string-append base (to-string i)))))
      (if (contains-sym? e s) (loop (+ i 1)) s))))

; одновременная замена символов по списку (старый . новый); головы выражений не трогаются
(define (rubi-rename e alist)
  (cond ((symbol? e) (let ((p (assoc e alist))) (if p (cdr p) e)))
        ((pair? e) (cons (car e) (map (lambda (a) (rubi-rename a alist)) (cdr e))))
        (else e)))

; Головы входного языка приводятся к степеням, как в Mathematica: Sqrt[u] — это Power[u,1/2],
; Exp[u] — Power[E,u]. Без этого правила Rubi не видят радикалов вовсе: `(^ (sqrt u) -1)` не
; сопоставляется с образцом `(^ (+ a (* b x)) 1/2)` — на замере 400 тяжёлых отказов таких 144.
(define (rubi-sqrt-head? e)
  (cond ((not (pair? e)) #f)
        ((equal? (car e) 'sqrt) #t)
        ((equal? (car e) 'exp) #t)
        (else (any? rubi-sqrt-head? (cdr e)))))

(define (rubi-normalize-heads u)
  (cond ((not (pair? u))
         ; RUBI.CH567.2: I в записи Mathematica — мнимая единица; в порте это %i. Без перевода
         ; int-check считает I параметром (значение 1,7) и верный ответ отвергается
         ; (t_5_3_6/213: exp(-3*I*atan(a+b*x))/x^3).
         (if (equal? u 'I) '%i u))
        ((equal? (car u) 'sqrt) (list '^ (rubi-normalize-heads (cadr u)) 1/2))
        ((equal? (car u) 'exp) (list '^ 'E (rubi-normalize-heads (cadr u))))
        (else (cons (car u) (rubi-normalize-heads-list (cdr u))))))

(define (rubi-normalize-heads-list l)
  (if (null? l) '() (cons (rubi-normalize-heads (car l)) (rubi-normalize-heads-list (cdr l)))))

; (u^p)^q = u^(p*q) при целом q — верно всегда; simplify оставляет 1/sqrt(u) как (^ (^ u 1/2) -1), и образцы
; вида (^ v n) его не видят.
(define (rubi-collapse-pow e)
  (if (not (pair? e))
      e
      (let ((a (map rubi-collapse-pow (cdr e))))
        (cond
          ((and (equal? (car e) (quote ^)) (= (length a) 2) (integer? (cadr a))
                (pair? (car a)) (equal? (car (car a)) (quote ^)) (= (length (car a)) 3) (number? (caddr (car a))))
           (list (quote ^) (cadr (car a)) (* (caddr (car a)) (cadr a))))
          ; RUBI.E1: (u v)^n = u^n v^n при целом n — верно всегда. Образцы 1/(Sqrt[a+b x] Sqrt[c+d x] Sqrt[e+f x])
          ; (1.1.1.3 #43-#48 и др., EllipticF/E) после sqrt -> ^ 1/2 имели вид (^ (* u^1/2 v^1/2 w^1/2) -1)
          ; и не сопоставлялись со степенями выражения.
          ((and (equal? (car e) (quote ^)) (= (length a) 2) (integer? (cadr a))
                (pair? (car a)) (equal? (car (car a)) (quote *)))
           (cons (quote *) (map (lambda (f) (rubi-collapse-pow (list (quote ^) f (cadr a)))) (cdr (car a)))))
          (else (cons (car e) a))))))

; RUBI.J1: сомножители с одинаковым основанием склеиваются, u^a u^b = u^(a+b) (a, b - числа): Mathematica делает это
; автоматически (Times - Flat/Orderless), а ac-norm - нет: 1/((x^2+c) Sqrt[x^2+c] Sqrt[x^2+c]) оставался
; произведением (u^-1)(u^-1) вместо u^-2. Верно на любой ветви: оба множителя - exp(показатель*Log u) с одним и тем же Log u.
; Числа и числовые основания не трогаются; нечисловой показатель - сомножитель остаётся как есть.
(define *rubi-merge-bases* #t)
(define (rubi-mb-split f)
  (cond ((number? f) (cons #f f))
        ((and (pair? f) (equal? (car f) '^) (= (length f) 3))
         (if (and (number? (caddr f)) (not (number? (cadr f)))) (cons (cadr f) (caddr f)) (cons #f f)))
        ((pair? f) (if (equal? (car f) '*) (cons #f f) (cons f 1)))
        ((symbol? f) (cons f 1))
        (else (cons #f f))))
(define (rubi-mb-add es b r)
  (cond ((null? es) (list (cons b r)))
        ((and (car (car es)) (equal? (car (car es)) b)) (cons (cons b (+ (cdr (car es)) r)) (cdr es)))
        (else (cons (car es) (rubi-mb-add (cdr es) b r)))))
(define (rubi-merge-prod fs)
  (let ((es (let loop ((l fs) (acc '()))
              (if (null? l)
                  acc
                  (let ((s (rubi-mb-split (car l))))
                    (loop (cdr l) (if (car s) (rubi-mb-add acc (car s) (cdr s)) (append acc (list s)))))))))
    (if (= (length es) (length fs))
        (cons '* fs)
        (let ((out (let loop ((l es) (acc '()))
                     (cond ((null? l) (reverse acc))
                           ((not (car (car l))) (loop (cdr l) (cons (cdr (car l)) acc)))
                           ((equal? (cdr (car l)) 0) (loop (cdr l) acc))
                           ((equal? (cdr (car l)) 1) (loop (cdr l) (cons (car (car l)) acc)))
                           (else (loop (cdr l) (cons (list '^ (car (car l)) (cdr (car l))) acc)))))))
          (cond ((null? out) 1)
                ((null? (cdr out)) (car out))
                (else (cons '* out)))))))
(define (rubi-merge-bases e)
  (if (not (pair? e))
      e
      (let ((a (map rubi-merge-bases (cdr e))))
        (if (equal? (car e) '*) (rubi-merge-prod a) (cons (car e) a)))))

; Сомножители с противоположными основаниями u и -u: основание -u записывается как (* -1 u).
; Тождество -a-b*x = (-1)(a+b*x) — просто перезапись, ветви не меняются; образцы 1.4.1 #29/#30
; (^ (* a v) m) (^ (* b v) n) требуют общего v. Правило применяется только к произведению, где пара есть.
(define (rubi-neg-sum? b1 b2 x)
  (and (pair? b1) (equal? (car b1) (quote +)) (pair? b2) (equal? (car b2) (quote +))
       (contains-sym? b1 x) (contains-sym? b2 x) (not (equal? b1 b2))
       (equal? (simplify (list (quote +) b1 b2)) 0)))

(define (rubi-factor-base f) (if (and (pair? f) (equal? (car f) (quote ^)) (= (length f) 3)) (cadr f) f))

(define (rubi-pair-neg-bases ne x)
  (if (and (pair? ne) (equal? (car ne) (quote *)))
      (let loop ((fs (cdr ne)) (done (quote ())) (changed #f))
        (if (null? fs)
            (if changed (cons (quote *) (reverse done)) ne)
            (let* ((f (car fs))
                   (b2 (rubi-factor-base f))
                   (g (and (pair? f) (equal? (car f) (quote ^))
                           (let find ((l done))
                             (cond ((null? l) #f)
                                   ((rubi-neg-sum? (rubi-factor-base (car l)) b2 x) (rubi-factor-base (car l)))
                                   (else (find (cdr l))))))))
              (if g
                  (loop (cdr fs) (cons (list (quote ^) (list (quote *) -1 g) (caddr f)) done) #t)
                  (loop (cdr fs) (cons f done) changed)))))
      ne))

; RUBI.S8: профиль в собственном времени. *rubi-p-int-acc* копит время прямых вложенных rubi-int
; внутри текущей правой части; rhs-us = время правой части за вычетом вложенных rubi-int
; (её утилиты: simplify, expand, деление многочленов). Включающее eval-us двойным счётом
; считало вложенное сопоставление в «правые части».
(define *rubi-p-int-acc* 0)
(define *rubi-p-rhs* 0)
(define *rubi-p-err* 0)   ; профиль: время от начала вычисления правой части до перехвата ошибки (включая вложенное)
; Rubi.m:477: Int[{u1, u2, ...}, x] := Map[Function[Int[#, x]], {u}] — интеграл списка поэлементно.
; Значение списка выражений в Lisp — пара без символа в голове; обычное выражение так не выглядит.
; Один неизвестный элемент делает неизвестным весь список (иначе теряется отказ вложенного Int).
(define (rubi-expression-list? e)
  (and (pair? e) (not (symbol? (car e)))))
; RUBI.CH567.3: диагностика «tainted» — какой ВЛОЖЕННЫЙ Int вернул unknown. При *rubi-unk-trace* каждый
; отказ подзадачи (глубина > 0) попадает в *rubi-unk-log* вместе с причиной отказа; первый по времени
; элемент задачи — самая глубокая (то есть настоящая) нерешаемая подзадача, внешние лишь пробрасывают unknown.
; Флаг по умолчанию #f, на поведение не влияет (только запись); список чистит вызывающий.
(define *rubi-unk-trace* #f)
(define *rubi-unk-log* '())
(define (rubi-int-note r ne)
  (if (and *rubi-unk-trace* (equal? r 'unknown) (> *rubi-depth* 0))
      (set! *rubi-unk-log* (cons (list ne *rubi-depth* *rubi-last-reason*) *rubi-unk-log*))))
(define (rubi-int-list l x)
  (if (null? l)
      '()
      (let ((r (rubi-int (car l) (car l) x)))
        (if (equal? r 'unknown)
            'unknown
            (let ((rest (rubi-int-list (cdr l) x)))
              (if (equal? rest 'unknown) 'unknown (cons r rest)))))))
(define (rubi-int ne orig x)
  (if (or (null? ne) (rubi-expression-list? ne))
      (rubi-int-list ne x)
  (if *rubi-prof*
      (let ((saved *rubi-p-int-acc*) (t0 (clock-us)))
        (set! *rubi-p-int-acc* 0)
        (let ((r (rubi-int-body ne orig x)))
          (set! *rubi-p-int-acc* (+ saved (- (clock-us) t0)))
          (rubi-int-note r ne)
          r))
      (let ((r (rubi-int-body ne orig x)))
        (rubi-int-note r ne)
        r))))

; RUBI.S15: переменная образца ?b в (* ?b x) и в Mathematica (Flat) берёт ВСЕ x-свободные множители, а ac-match -
; ровно один (match.lisp: ?x - один аргумент). Поэтому в слагаемых суммы x-свободные множители группируются во
; вложенное произведение: (+ a (* -1 r x)) -> (+ a (* (* -1 r) x)); без этого a + b*x с b = -r*s, c - a*d/b + ...
; (все подзадачи после подстановок) не находили ни одного правила.
(define *rubi-group-free* #t)
(define *rubi-group-free-sum* #t)   ; RUBI.D3: то же для слагаемых суммы (флаг - для сравнения до/после)
(define (rubi-group-term t x)
  (if (and (pair? t) (equal? (car t) '*))
      (let ((free (filter (lambda (f) (not (contains-sym? f x))) (cdr t)))
            (dep (filter (lambda (f) (contains-sym? f x)) (cdr t))))
        (if (and (pair? free) (pair? (cdr free)) (pair? dep))
            (cons '* (cons (cons '* free) dep))
            t))
      t))
(define (rubi-group-free e x)
  (cond ((not (pair? e)) e)
        ((not (contains-sym? e x)) e)
        ((equal? (car e) '+)
         (let* ((ts (map (lambda (t) (rubi-group-term (rubi-group-free t x) x)) (cdr e)))
                (free (filter (lambda (t) (not (contains-sym? t x))) ts))
                (dep (filter (lambda (t) (contains-sym? t x)) ts)))
           ; RUBI.D3: Plus в Mathematica - Flat: `a_ + b_.*x_^2` берёт ВСЕ x-свободные слагаемые как a_
           ; (c - a*d/b + d*x^2/b: a = c - a*d/b); ac-match связывает ?a с одним слагаемым - группируем
           ; x-свободные слагаемые во вложенную сумму, как x-свободные множители выше
           (if (and *rubi-group-free-sum* (pair? free) (pair? (cdr free)) (pair? dep))
               (cons '+ (cons (cons '+ free) dep))
               (cons '+ ts))))
        ; RUBI.CH3.2: показатель экспоненты F^(c d x) — тот же Flat: g_.*(e_.+f_.*x_) берёт ВСЕ x-свободные множители
        ; (правила 2.1/2.3: F^(g (e+f x)), F^(c v)); без группировки exp(-4 x/n)*(a+b x)^p не находило ни одного правила
        ((and (equal? (car e) '^) (= (length e) 3) (not (contains-sym? (cadr e) x)))
         (list '^ (cadr e) (rubi-group-term (rubi-group-free (caddr e) x) x)))
        (else (cons (car e) (map (lambda (a) (rubi-group-free a x)) (cdr e))))))
; RUBI.SYM.4: Mathematica сводит отрицательную степень тригонометрической функции к обратной голове
; (1/Cos[u] -> Sec[u], 1/Sin[u] -> Csc[u], 1/Tan[u] -> Cot[u], и обратно: 1/Sec[u] -> Cos[u]), причём
; Sec[u]^2 и 1/Cos[u]^2 — один и тот же объект, поэтому правило не может их различить. Вход задачи
; приходит от упрощателя порта уже в старой форме (sec -> cos^-1), а образцы правил Rubi написаны
; головами sec/csc/cot (tools/rubi/precompute.mjs, единая форма). Без возврата к головам под *rubi-nf*
; не срабатывало, например, правило 4.5.1.2 для ∫sec^2/(a sec + a) (REPORT-RUBI-SYM4.md).
(define (rubi-recip-heads e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) '^) (= (length e) 3) (integer? (caddr e)) (< (caddr e) 0)
              (pair? (cadr e)) (= (length (cadr e)) 2)
              (member? (car (cadr e)) '(sin cos tan sec csc cot)))
         (let* ((h (car (cadr e))) (arg (rubi-recip-heads (cadr (cadr e))))
                (n (- 0 (caddr e)))
                (rh (cond ((equal? h 'sin) 'csc) ((equal? h 'cos) 'sec) ((equal? h 'tan) 'cot)
                          ((equal? h 'csc) 'sin) ((equal? h 'sec) 'cos) (else 'tan))))
           (if (equal? n 1) (list rh arg) (list '^ (list rh arg) n))))
        (else (cons (car e) (map rubi-recip-heads (cdr e))))))
; RUBI.NF: норма входа одной функцией формы на всём пути Rubi (вход задачи, подзадачи, правые части).
; Под флагом — rubi-nf (автовычисление Mathematica, без тождеств); без флага — прежняя цепочка
; normalize-heads → collapse-pow → merge-bases → ac-norm → strip-units → pair-neg-bases (сравнение вкл/выкл).
(define (rubi-norm-input ne x)
  (if *rubi-nf*
      (let ((n (rubi-nf ne)))
        ; RUBI.TRIG: под *rubi-trig-nf* форма ядра, обратного перевода cos^-n -> sec нет
        (if (or *rubi-trig-nf* *rubi-recip-off*) n (rubi-recip-heads n)))
      (rubi-pair-neg-bases
       (ac-strip-units
        (ac-norm (let ((cp (rubi-collapse-pow (if (or (rubi-sqrt-head? ne) (contains-sym? ne (quote I)))
                                             (rubi-normalize-heads ne) ne))))
                        (if *rubi-merge-bases* (rubi-merge-bases cp) cp))))
       x)))
; RUBI.SYM.2: защита от цикла по паре (выражение, переменная) — как active_integral_hit эталона
; (symbolica-integrate, src/lib.rs:677-691, MIT): Int[v, x] внутри вычисления Int[u, x] при v = u — цикл,
; ответ unknown. Раньше цикл ловила только глубина rubi-max-depth (32) — она же ограничивает законные
; цепочки правил, поэтому порог приходилось держать большим, а самоповтор на другой глубине не ловился.
(define *rubi-cycle-guard* #f)          ; RUBI.SYM.2.2: защита от цикла по (выражение, переменная) — выключена, см. rubi-int-body
(define *rubi-active* (make-hash))       ; (выражение переменная) -> сколько раз на текущей цепочке
(define (rubi-active-hit? ne x) (> (hash-ref *rubi-active* (list ne x) 0) 0))
(define (rubi-active-push ne x)
  (let* ((k (list ne x)) (n (+ 1 (hash-ref *rubi-active* k 0))))
    (hash-set! *rubi-active* k n)))
(define (rubi-active-pop ne x)
  (let* ((k (list ne x)) (n (- (hash-ref *rubi-active* k 0) 1)))
    (if (<= n 0) (hash-remove! *rubi-active* k) (hash-set! *rubi-active* k n))))
; RUBI.SYM.3: в порте нет базовых правил 6.1.1-6.1.9 исходника (∫Sinh^n, ∫Cosh^n и их линейные
; аргументы): в эталоне (symbolica-integrate, src/rules/rubi_6_1_12_hyperbolic_functions.rs и др.)
; Sinh/Cosh обрабатываются правилами главы 6 напрямую. Порт закрывает этот пробел шлюзом
; DeactivateTrig (гиперболические клаузы IUF.m:6210-6218) — но шлюз стоит ПОСЛЕ перебора всех правил,
; а выражение с sinh/cosh совпадает с 589 кандидатами (главы 1-4), у которых на холодную ещё и
; образцы не скомпилированы: ∫sinh x не укладывалось в бюджет (≈1,5 с против 0,5 с остатка после
; загрузки правил). Поэтому для выражений с гиперболическими головами шлюз пробуется ДО перебора:
; он переписывает их в тригонометрию мнимого аргумента (та же форма, что даёт входной упрощатель без
; *rubi-nf*, — старый путь порта), а если форма не изменилась, перебор правил идёт как обычно.
(define (rubi-hyp-head? e)
  (cond ((not (pair? e)) #f)
        ((and (member? (car e) (rubi-hyperbolic-heads)) (pair? (cdr e))) #t)
        (else (any? rubi-hyp-head? (cdr e)))))
(define (rubi-int-body ne orig x)
  (if *rubi-prof* (set! *rubi-p-calls* (+ *rubi-p-calls* 1)))
  (let* ((tn (and *rubi-prof* (clock-us)))
         (ne (let ((n0 (rubi-norm-input ne x)))
               (if *rubi-group-free* (rubi-group-free n0 x) n0)))
         (_ (if tn (set! *rubi-p-norm* (+ *rubi-p-norm* (- (clock-us) tn))))))
    (cond
      ; RUBI.SYM.2: самоповтор интеграла на текущей цепочке — цикл шлюза/правила, а не задача
      ; выключено по умолчанию (*rubi-cycle-guard* #f): пилот defd37c −2 402 (1 702 быстрых потери) — наша
      ; нормализация сводит к одному ne разные для Rubi формы, и законный шаг правила выглядел циклом
      ((and *rubi-cycle-guard* (rubi-active-hit? ne x)) (rubi-fail 'cycle))
      ; детерминированный бюджет: предел числа попыток сопоставления на задачу
      ((> *rubi-tries* *rubi-tries-limit*) (rubi-fail 'tries))
      ((> *rubi-depth* rubi-max-depth) (rubi-fail 'depth))
      (#t
       (rubi-active-push ne x)
       (unwind-protect
        (let ((memo (hash-ref *rubi-memo* ne #f)))
          (if memo
              (cdr memo)
              (let ((r (let ((base (rubi-base-int ne x)))
                         (if base
                             base
                             (begin
                               (if *rubi-seen* (set! *rubi-seen* (cons ne *rubi-seen*)))
                               ; RUBI.SYM.3: гиперболические головы — шлюз до перебора (см. rubi-hyp-head?)
                               ; RUBI.GW.ORDER: как правило 4.1.0.1 #1 в Rubi — шлюз DeactivateTrig стоит
                               ; перед остальными правилами главы 4; под #t для функций тригонометрии
                               ; линейного аргумента зовём его до перебора, иначе распознаватели 4.7.5/3.5
                               ; сжигают бюджет (cos^(-k/2), sec^(k/2)).
                               (let* ((hg (cond ((and *rubi-nf* (rubi-hyp-head? ne)) (rubi-gateway ne x))
                                                ((and *rubi-nf* (rubi-trig-gateway-early? ne x))
                                                 (rubi-gateway-deact ne x))
                                                (else 'unknown)))
                                      ; RUBI.SYM.2: перебор правил, и только после его отказа — шлюз DeactivateTrig
                                      (lr (if (not (equal? hg 'unknown)) hg (rubi-loop ne orig x))))
                                 (if (equal? lr 'unknown) (rubi-gateway ne x) lr)))))))
                ; RUBI.SYM.2: кэш подзадач на корневой вызов — аналог cached_integral эталона
                ; (symbolica-integrate, src/lib.rs:680, MIT). Успех кэшируется всегда; детерминированный
                ; отказ (нет подходящего правила, цикл, отказ шлюза) — тоже, чтобы повторная подзадача не
                ; пересчитывалась. Отказы по бюджету/лимиту попыток/глубине зависят от контекста и в кэш
                ; не пишутся (прежнее поведение).
                (cond ((not (equal? r 'unknown)) (hash-set! *rubi-memo* ne (cons #t r)))
                      ((member? *rubi-last-reason* '(no-rule cycle gateway gateway-seen))
                       (hash-set! *rubi-memo* ne (cons #f r))))
                r)))
        (rubi-active-pop ne x))))))

; Базовые определения Int из ядра Rubi (Kernel/*.mx, в .m-правилах их нет):
; константа, линейность суммы, вынесение множителя, не зависящего от x.
(define (rubi-base-int e x)
  (cond ((not (contains-sym? e x)) (list '* e x))
        ((and (pair? e) (equal? (car e) '+)) (rubi-sum-int (cdr e) x))
        ((and (pair? e) (equal? (car e) '*)) (rubi-prod-int (cdr e) x))
        ((and (pair? e) (equal? (car e) 'sin)) (rubi-base-trig e x 'cos -1))
        ((and (pair? e) (equal? (car e) 'cos)) (rubi-base-trig e x 'sin 1))
        (else #f)))

; ∫sin(u) = -cos(u)/d и ∫cos(u) = sin(u)/d при линейном u = c + d*x, c и d не зависят от x.
; В Rubi это правила инертных функций после DeactivateTrig (cos сводится к sin(u + Pi/2));
; прямого правила Int[Cos[c_. + d_.*x_]] в IntegrationRules нет.
; RUBI.HYP: коэффициент d берётся PolynomialQ+Coeff (LinearQ, IUF.m:1373), а не ac-match по
; `(+ ?c (* ?d x))`: после гиперболических клауз DeactivateTrigAux (IUF.m:6210-6218) d = I*b —
; произведение из двух множителей, а ?d в ac-match связывается только с одним (lib/match.lisp,
; отдельная карточка) — из-за этого cosh(a+b x) уходил в экспоненциальную форму.
(define (rubi-base-trig e x res sign)
  (and (= (length (cdr e)) 1)
       (let ((u (cadr e)))
         (and (rubi-linearq u x)
              (let ((d (try (coeff u x 1) (lambda (err) #f))))
                (and d (not (contains-sym? d x)) (not (equal? d 0))
                     (list '* (list '/ sign d) (list res u))))))))

(define (rubi-sum-int terms x)
  (if (null? terms)
      0
      (let ((r (rubi-int (car terms) (car terms) x)))
        (if (equal? r 'unknown)
            'unknown
            (let ((rest (rubi-sum-int (cdr terms) x)))
              (cond ((equal? rest 'unknown) 'unknown)
                    ((equal? rest 0) r)
                    (else (list '+ r rest))))))))

; (b*x^n)^p при дробном рациональном p: (b x^n)^p = b^IntPart(p) (b x^n)^FracPart(p) / x^(n FracPart(p)) * x^(n p).
; Правило Rubi 1.1.2.1 #1 / 1.1.2.3, но для сомножителя произведения (образцы правил видят только голую степень).
; Множитель перед интегралом постоянен по x (кусочно), int-check проверяет итог дифференцированием.
(define (rubi-xpow-parts f x)
  (and (pair? f) (equal? (car f) (quote ^)) (= (length f) 3) (rubi-fractionq (caddr f))
       (pair? (cadr f)) (equal? (car (cadr f)) (quote *))
       (let* ((ts (cdr (cadr f)))
              (xs (filter (lambda (t) (contains-sym? t x)) ts))
              (bs (filter (lambda (t) (not (contains-sym? t x))) ts)))
         (and (= (length xs) 1)
              (let ((xp (car xs)))
                (cond ((equal? xp x) #f)   ; (b*x)^p уже берут правила 1.1.1.x
                      ((and (pair? xp) (equal? (car xp) (quote ^)) (equal? (cadr xp) x) (integer? (caddr xp)) (> (caddr xp) 1))
                       (list (if (null? bs) 1 (if (null? (cdr bs)) (car bs) (cons (quote *) bs))) (caddr xp)))
                      (else #f)))))))

(define (rubi-xpow-hit? rest x)
  (any? (lambda (f) (rubi-xpow-parts f x)) rest))

(define (rubi-try-xpow const rest x)
  (let ((hit (let find ((l rest)) (cond ((null? l) #f) ((rubi-xpow-parts (car l) x) (car l)) (else (find (cdr l)))))))
    (and hit
         (let* ((parts (rubi-xpow-parts hit x)) (b (car parts)) (n (cadr parts)) (p (caddr hit))
                (ip (floor p)) (fp (- p (floor p)))
                (others (filter (lambda (f) (not (equal? f hit))) rest))
                (inner (cons (quote *) (cons (list (quote ^) x (* n p)) others)))
                (inner (if (null? others) (list (quote ^) x (* n p)) inner))
                (r (rubi-int inner inner x)))
           (if (equal? r (quote unknown))
               (quote unknown)
               (cons (quote *)
                     (append const
                             (list (list (quote /) (list (quote *) (list (quote ^) b ip) (list (quote ^) (list (quote *) b (list (quote ^) x n)) fp))
                                         (list (quote ^) x (* n fp)))
                                   r))))))))

(define (rubi-prod-int factors x)
  (let loop ((fs factors) (const '()) (rest '()))
    (cond ((null? fs)
           (cond ((null? rest) #f)
                 ((and (pair? rest) (rubi-xpow-hit? rest x)) (rubi-try-xpow const rest x))
                 ; множитель, не зависящий от x, выносится при любом числе x-зависимых:
                 ; иначе ∫3x√(1+x) уходил в перебор правил по всему произведению
                 ((null? const)
                  (if (= (length rest) 1)
                      (rubi-int (car rest) (car rest) x)
                      #f))
                 (else
                  (let* ((inner (if (= (length rest) 1) (car rest) (cons '* rest)))
                         (r (rubi-int inner inner x)))
                    (if (equal? r 'unknown) 'unknown
                        (list '* (cons '* const) r))))))
          ((contains-sym? (car fs) x) (loop (cdr fs) const (cons (car fs) rest)))
          (else (loop (cdr fs) (cons (car fs) const) rest)))))

; профиль: время отсева кандидатов (головы, форма, стек, таблица неудач) без сопоставления
(define *rubi-p-scan* 0)
(define (rubi-scan-skip ts v)
  (if (and v ts) (set! *rubi-p-scan* (+ *rubi-p-scan* (- (clock-us) ts))))
  v)

; ---------- RUBI.SYM.2: шлюз DeactivateTrig как фаза движка ----------
; Эталон (symbolica-integrate, MIT): шлюз живёт в integrate_view_scan_rules — сначала перебираются ВСЕ
; правила, и только если ни одно не дало ответа, вызывается DeactivateTrig; ответ принимается, если форма
; изменилась и он «готовая первообразная» (rubi_finished_primitive_q, src/lib.rs:10917).
; В порте ту же роль играло правило «Rubi 4.1.0.1 #1», но оно стоит в таблице и потому срабатывает ДО
; правил своей главы (4.1 < 4.5): sec^2/(a sec+a) получало уже переписанную форму, и 4.5.1.2 теряло ответ.
; Теперь правило из перебора исключается (rubi-gateway-candidate?), а шлюз вызывается после rubi-loop.
; *rubi-gateway* — выключатель для сравнения «как было» (со шлюзом-правилом).
(define *rubi-gateway* #t)
(define *rubi-gateway-id* "Rubi 4.1.0.1 #1")
(define *rubi-gw-seen* (make-hash))      ; выражение -> #t: шлюз на нём уже срабатывал (защита от осцилляции)
(define (rubi-gateway-candidate? r)
  (and *rubi-gateway* (equal? (nth r 1) *rubi-gateway-id*)))
; Ответ — «готовая первообразная»: без меток отказа и без невычисленного Int.
(define (rubi-finished-primitive? r)
  (not (or (equal? r 'unknown)
           (rubi-tainted? r)
           (and (pair? r) (equal? (car r) 'integrate)))))
; RUBI.NF.CH48: под единой формой sec/csc/cot остаются головами, а правила 4.1.x/4.2.x записаны для
; cos^-n/sin^-n: смешанные формы (sec^n вместе с sin/cos/tan) отказывают, тогда как старая форма (#f)
; нормировала sec -> cos^-1 на входе. Шлюз после перебора переводит reciprocal-головы в степени партнёра
; (как #f), не меняя основной путь #t: сначала пробуются правила 4.3/4.5/4.7 на головах.
(define (rubi-recip-partner h)
  (cond ((equal? h 'sec) 'cos) ((equal? h 'csc) 'sin) ((equal? h 'cot) 'tan) (else #f)))
(define (rubi-recip-to-powers e)
  (cond ((not (pair? e)) e)
        ((equal? (car e) 'quote) e)
        ; положительная степень cos -> sin(u+pi/2), как нормировка старой формы (#f); cos^-n (из sec) не трогаем
        ((and (null? (cddr e)) (equal? (car e) 'cos))
         (list 'sin (list '+ (rubi-recip-to-powers (cadr e)) (list '* 1/2 'pi))))
        ((and (equal? (car e) '^) (= (length e) 3) (pair? (cadr e)) (null? (cddr (cadr e)))
              (equal? (car (cadr e)) 'cos) (number? (caddr e)) (> (caddr e) 0))
         (list '^ (list 'sin (list '+ (rubi-recip-to-powers (cadr (cadr e))) (list '* 1/2 'pi))) (caddr e)))
        ((and (null? (cddr e)) (rubi-recip-partner (car e)))
         (list '^ (list (rubi-recip-partner (car e)) (rubi-recip-to-powers (cadr e))) -1))
        ((and (equal? (car e) '^) (= (length e) 3) (pair? (cadr e)) (null? (cddr (cadr e)))
              (rubi-recip-partner (car (cadr e))))
         (let ((n (caddr e)) (b (cadr (cadr e))))
           (list '^ (list (rubi-recip-partner (car (cadr e))) (rubi-recip-to-powers b))
                 (if (number? n) (- 0 n) (list '- n)))))
        (else (cons (car e) (map rubi-recip-to-powers (cdr e))))))
(define (rubi-recip-head-present? e)
  (cond ((not (pair? e)) #f)
        ((and (null? (cddr e)) (rubi-recip-partner (car e))) #t)
        (else (any? rubi-recip-head-present? (cdr e)))))
(define (rubi-plain-trig-present? e)
  (cond ((not (pair? e)) #f)
        ((and (null? (cddr e)) (member? (car e) '(sin cos tan))) #t)
        (else (any? rubi-plain-trig-present? (cdr e)))))
(define (rubi-recip-gateway? ne)
  (and *rubi-nf* (rubi-recip-head-present? ne) (rubi-plain-trig-present? ne)))
; чистые cos-формы (главы 4.2 без sec): старая форма нормировала cos -> sin(u+pi/2), правила 4.1.x брали
(define (rubi-cos-positive-present? e)
  (cond ((not (pair? e)) #f)
        ((and (null? (cddr e)) (equal? (car e) 'cos)) #t)
        ((and (equal? (car e) '^) (= (length e) 3) (pair? (cadr e)) (null? (cddr (cadr e)))
              (equal? (car (cadr e)) 'cos) (number? (caddr e)) (> (caddr e) 0)) #t)
        (else (any? rubi-cos-positive-present? (cdr e)))))
(define (rubi-cos-gateway? ne)
  (and *rubi-nf* (not (rubi-recip-head-present? ne)) (rubi-cos-positive-present? ne)))
; шлюз возвращает форму старого вида (cos^-n): на время его Int обратный перевод rubi-recip-heads выключен
(define *rubi-recip-off* #f)
; RUBI.GW.ORDER: локальные копии предикатов utils-c (файл главы 4 грузится лениво, а символы движка
; должны разрешаться при загрузке модуля — ModuleTests): «есть голова тригонометрии» и
; FunctionOfTrigOfLinearQ (IUF.m:4358).
(define (rubi-trig-head-local? u)
  (cond ((not (pair? u)) #f)
        ((member? (car u) (rubi-trig-heads)) #t)
        (else (any? rubi-trig-head-local? (cdr u)))))
(define (rubi-trig-of-linear-local-q u x)
  (cond ((not (pair? u)) #t)
        ((member? (car u) (rubi-trig-heads))
         (or (rubi-freeq (cadr u) x) (rubi-linearq (cadr u) x)))
        ((member? (car u) (list '+ '- '* '/ '^))
         (every? (lambda (e) (rubi-trig-of-linear-local-q e x)) (cdr u)))
        (else #f)))
; RUBI.GW.ORDER: тригонометрия под степенью суммы ((a+b*tan)^n, sqrt(a+b*sec^2)) — не ранний путь:
; DeactivateTrig там меняет форму, но Int переписанной формы уходит в ветвящиеся ответы и/или
; сжигает бюджет; такие задачи перебор решает в исходной форме (замер среза 4: 6 потерь из 7).
(define (rubi-trig-sum-power? e)
  (cond ((not (pair? e)) #f)
        ((equal? (car e) 'quote) #f)
        ((and (equal? (car e) '^) (= (length e) 3) (pair? (cadr e)) (equal? (car (cadr e)) '+)
              (rubi-trig-head-local? (cadr e))) #t)
        (else (any? rubi-trig-sum-power? (cdr e)))))
; tan/cot рано не трогаем: шлюз для них не нужен (цель — cos/sec-степени), а переписывание
; tan^(3/2)-форм уводит перебор в долгий путь (замер: 2068→4601 мс, потеря у границы).
(define (rubi-tan-head-present? e)
  (cond ((not (pair? e)) #f)
        ((and (null? (cddr e)) (member? (car e) '(tan cot))) #t)
        (else (any? rubi-tan-head-present? (cdr e)))))
; RUBI.GW.ORDER: ранний шлюз — только для функций тригонометрии линейного аргумента (FunctionOfTrigOfLinearQ,
; IUF.m:4358) и только если он ещё не срабатывал на этом выражении: иначе цикл «cos -> sin(x+pi/2) -> cos».
(define (rubi-trig-gateway-early? ne x)
  (and *rubi-gateway*
       (not (hash-ref *rubi-gw-seen* ne #f))
       (not (rubi-trig-sum-power? ne))
       (not (rubi-tan-head-present? ne))
       (rubi-trig-head-local? ne)
       (rubi-trig-of-linear-local-q ne x)))
(define (rubi-gateway ne x) (rubi-gateway* ne x #t))
; RUBI.GW.ORDER: ранний путь — только переписывание DeactivateTrig (правило 4.1.0.1 #1); фолбэк
; CH48 (sec/csc/cot -> степени партнёра, cos -> sin(u+pi/2)) остаётся на пути после перебора:
; иначе произведения sec/tan, которые DeactivateTrig не меняет, уходили в чужой путь и теряли бюджет.
(define (rubi-gateway-deact ne x) (rubi-gateway* ne x #f))
(define (rubi-gateway* ne x allow-convert)
  (if (or (not *rubi-gateway*) (hash-ref *rubi-gw-seen* ne #f))
      (rubi-fail 'gateway-seen)
      (let* ((d0 (rubi-deactivate-trig ne x))
             (g (and allow-convert (equal? d0 ne)
                     (or (rubi-recip-gateway? ne) (rubi-cos-gateway? ne))))
             (d (if g (rubi-recip-to-powers ne) d0)))
        (cond ((equal? d ne) (rubi-fail 'no-rule))
              (#t
               (hash-set! *rubi-gw-seen* ne #t)
               (let ((r (if g
                            (begin
                              (set! *rubi-recip-off* #t)
                              (unwind-protect (rubi-int d d x) (set! *rubi-recip-off* #f)))
                            (rubi-int d d x))))
                 (if (rubi-finished-primitive? r) r (rubi-fail 'gateway))))))))

; RUBI.S8: отсев по головам и форме зависит только от выражения; список прошедших кэшируется на выражение
; (одно и то же подвыражение ищется повторно, а отсев 2,7 тыс. кандидатов стоил 20-70 мс на проход)
; RUBI.S8 + RUBI.SPEED: отсев по головам и форме зависит только от выражения; список прошедших и
; производные величины (xc, exps) кэшируются на выражение. Головы и кандидаты считаются здесь же:
; раньше rubi-int-body звал rubi-candidates (свой кэш по тому же выражению) — лишний обход и хеш.
(define (rubi-loop ne orig x)
  (let* ((ts (and *rubi-prof* (clock-us)))
         (cached (hash-ref *rubi-cands2* ne #f))
         (ent (or cached
                  (let* ((heads (rubi-expr-heads ne '()))
                         (hs (rubi-head-set heads))
                         (bcands (rubi-candidates ne heads))
                         (xc (rubi-expr-xfactors ne x))
                         (exps (rubi-expr-exponents ne '()))
                         ; RUBI.INDEX: набор структурных признаков выражения — один раз на выражение
                         (ifeats (and *rubi-index* (rubi-expr-feats ne)))
                         (cs (filter (lambda (r) (and (not (rubi-gateway-candidate? r))
                                                      (rubi-prefilter-set? (nth r 6) hs)
                                                      (or (rubi-root-ok? (rubi-rule-root-key r) ne)
                                                          (rubi-root-suspect? r ne))
                                                      (rubi-shape-ok? r xc exps)
                                                      (or (rubi-feats-ok? r ifeats)
                                                          (rubi-index-suspect? r ne ifeats))))
                                     bcands)))
                    (if (and *rubi-prof* ifeats)
                        (set! *rubi-p-idxn* (+ *rubi-p-idxn* (- (length bcands) (length cs)))))
                    (hash-set! *rubi-cands2* ne (list cs xc exps))
                    (if *rubi-prof*
                        (begin (set! *rubi-p-candmiss* (+ *rubi-p-candmiss* 1))
                               (set! *rubi-p-candn* (+ *rubi-p-candn* (length cs)))))
                    (list cs xc exps))))
         (cs (car ent)) (xc (cadr ent)) (exps (caddr ent))
         (_ (rubi-scan-skip ts #f)))
    (if *rubi-trace*
        (begin (if (not (hash-ref *rubi-trace-nc* ne #f))
                   (begin (rubi-trace-add (list 'seen ne))
                          ; RUBI.C1: цепочка - правило и родительское выражение, породившие подзадачу
                          (rubi-trace-add (list 'chain ne (if (pair? *rubi-stack*) (car *rubi-stack*) #f)))))
               (hash-set! *rubi-trace-nc* ne (length cs))))
    ; в loop* параметр heads — таблица неудач для этого выражения (id -> #t): хешируется только строка id
    (if (and *rubi-prof* cached) (set! *rubi-p-candhit* (+ *rubi-p-candhit* 1)))
    (rubi-loop* cs ne orig x
                (or (hash-ref *rubi-failed* ne #f)
                    (let ((h (make-hash))) (hash-set! *rubi-failed* ne h) h))
                xc exps)))

; Правило id уже трижды на стеке, и размеры (rubi-leaf-count) его выражений вместе с текущим строго растут, причём
; текущее больше самого раннего из трёх не меньше чем в 1,5 раза. Стек: новые в голове, элемент (id выражение).
(define *rubi-growth-fuse* #t)
(define (rubi-growth-cycle? id ne)
  (and *rubi-growth-fuse*
       (let loop ((l *rubi-stack*) (es '()))
         (cond ((null? l)
                (and (>= (length es) 3)
                     (let* ((e1 (car es)) (e2 (cadr es)) (e3 (caddr es))
                            (n (rubi-leaf-count ne)) (l1 (rubi-leaf-count e1))
                            (l2 (rubi-leaf-count e2)) (l3 (rubi-leaf-count e3)))
                       (and (> n l1) (> l1 l2) (> l2 l3) (>= (* 2 n) (* 3 l3))))))
               ((equal? (car (car l)) id) (loop (cdr l) (if (< (length es) 3) (append es (list (cadr (car l)))) es)))
               (else (loop (cdr l) es))))))

; EX.EXPLAIN: рамка шага правила Rubi — только если журнал правил включён (*rubi-step-log*).
; При #f тело выполняется как обычно (стек/глубина/обработка ошибок — в теле), но ни шага, ни попытки нет.
(define (rubi-rule-step id orig x thunk)
  (if *rubi-step-log*
      (with-step ('rubi-step (if (string-contains? id "Rubi ") id (string-append "Rubi " id))
                              ; STEPS.NF: «до» — интеграл (int/dx f), а не подынтегральная f:
                              ; шаг правила — переход к первообразной, checkSteps проверяет
                              ; d/dx(после) = f; иначе проверка сравнивала f с ответом и
                              ; объявляла ложными все шаги Rubi.
                              (list (string->symbol (string-append "int/d" (to-string x))) orig))
                 (thunk))
      (thunk)))


(define (rubi-loop* cands ne orig x heads xc exps)
  (if (null? cands)
      (begin
        (if *rubi-trace*
            (let ((cf (hash-ref *rubi-trace-cf* ne '())))
              (rubi-trace-add (list 'dead ne (hash-ref *rubi-trace-nc* ne 0) (length cf)))
              (for-each (lambda (c) (rubi-trace-add (list 'cond-fail (car c) (cadr c) (caddr c) ne))) cf)))
        (rubi-fail 'no-rule))
      (let* ((r (car cands))
             (id (nth r 1)) (req (nth r 6))
             (key (list id ne)) (ts (and *rubi-prof* (clock-us))))
        (cond
          ; отсев по головам и форме сделан в rubi-loop (кэш на выражение): здесь только стек и таблица неудач
          
          ; пара «правило + выражение» уже на стеке — правило зацикливается
          ((rubi-scan-skip ts (member? key *rubi-stack*)) (rubi-loop* (cdr cands) ne orig x heads xc exps))
          ; предохранитель RUBI.C1 (не исправление причины): то же правило в четвёртый раз по цепочке с монотонно
          ; растущей формой (коэффициенты вида b c/(b c - a d) без сокращения: 1.1.1.3 #69/#72, 1.1.1.2 #39, ...)
          ((rubi-scan-skip ts (rubi-growth-cycle? id ne))
           (if *rubi-trace* (rubi-trace-add (list 'growth id ne)))
           (rubi-loop* (cdr cands) ne orig x heads xc exps))
          ; RUBI.BACKTRACK: перебор главы 9 на этом подвыражении исчерпал предел попыток
          ((rubi-bt-9x-skip ne id)
           (if *rubi-trace* (rubi-trace-add (list 'no9 id ne)))
           (rubi-loop* (cdr cands) ne orig x heads xc exps))
          ; детерминированная неудача этого правила на этом выражении в текущем вызове
          ((rubi-scan-skip ts (hash-ref heads id #f))
           (set! *rubi-cache-hits* (+ *rubi-cache-hits* 1))
           (rubi-loop* (cdr cands) ne orig x heads xc exps))
          (#t
           (set! *rubi-tries* (+ *rubi-tries* 1))
           (if *rubi-trace* (set! *rubi-trace-ne* ne))
           (let* ((tm (and *rubi-prof* (clock-us)))
                  (binds (try (ac-match-prepared (rubi-prepared r) ne (rubi-cond-fn r))
                              (lambda (err) 'rubi-match-error)))
                  ; RUBI.C11.2: совпадение получено групповой привязкой (Flat Times, lib/match.lisp
                  ; ac-group-used?) — к нему «первое правило окончательно» не применяется: правило,
                  ; совпавшее только группировкой, может увести в тупик (rhs-fail «4.1.7 #8» на задаче
                  ; 4.1.7/454 из loss-c11), а следующее правило файла («4.1.7 #30») даёт ответ.
                  (grouped (and binds (not (equal? binds 'rubi-match-error)) (ac-group-used?))))

             (if tm
                 (begin (set! *rubi-p-match* (+ *rubi-p-match* (- (clock-us) tm)))
                        (set! *rubi-p-matches* (+ *rubi-p-matches* 1))))
             (if (and binds (not (equal? binds 'rubi-match-error)))
                 (begin (set! *rubi-last-rule* id)
                        (if *rubi-prof* (set! *rubi-matched* (cons id *rubi-matched*)))
                        (if (and *rubi-trace* *rubi-debug-binds* (equal? id *rubi-debug-binds*))
                            (rubi-trace-add (list 'binds id ne (format "~s" binds))))))
             (if (not (and binds (not (equal? binds 'rubi-match-error))))
                 (begin (hash-set! heads id #t)
                        (rubi-loop* (cdr cands) ne orig x heads xc exps))
                 (let* ((te (and *rubi-prof* (clock-us)))
                        (ans
                         (rubi-rule-step id orig x
                          (lambda ()
                           (try
                            (begin
                              (set! *rubi-stack* (cons key *rubi-stack*))
                              (set! *rubi-depth* (+ *rubi-depth* 1))
                              (let ((v (begin (set! *rubi-cur-id* id) (rubi-eval (cdr (rubi-fixed r)) binds))))
                                (set! *rubi-depth* (- *rubi-depth* 1))
                                (set! *rubi-stack* (cdr *rubi-stack*))
                                v))
                            (lambda (err)
                              ; причина привязывается к правилу: по одной ошибке не видно, чья она
                              (if te (set! *rubi-p-err* (+ *rubi-p-err* (- (clock-us) te))))
                              (if *rubi-trace* (set! *rubi-trace-err* (to-string err)))
                              (set! *rubi-depth* (if (> *rubi-depth* 0) (- *rubi-depth* 1) 0))
                              (if (pair? *rubi-stack*) (set! *rubi-stack* (cdr *rubi-stack*)))
                              ; RUBI.RULE d: деление на ноль в правой части — у Mathematica это ComplexInfinity,
                              ; а не исключение (1.2.2.4 #39: коэффициент содержит 1/(a f^2 (m+1)) при a=0).
                              ; Такой ответ недействителен: правило отвергается, как unknown вложенного Int.
                              (if (string-contains? (to-string err) "Деление на ноль")
                                  'complex-infi
                                  (begin
                                    (let ((m (string-append id " | " (to-string err))))
                                      (hash-set! *rubi-errors* m (+ 1 (hash-ref *rubi-errors* m 0))))
                                    'rubi-eval-error))))))))
                   (if te
                       (begin (set! *rubi-p-eval* (+ *rubi-p-eval* (- (clock-us) te)))
                              (set! *rubi-p-step* (+ *rubi-p-step* (max 0 (- (- (clock-us) te) *rubi-last-dt*))))
                              (set! *rubi-p-evals* (+ *rubi-p-evals* 1))))
                   (cond ((or (equal? ans 'complex-infi) (and (pair? ans) (rubi-tainted? ans))
                               ; RUBI.CH567.2: правая часть свернула метку отказа в ноль — -i/2*Int[u]+i/2*Int[u]
                               ; при Int[u] = unknown даёт 0 (4.1.10 #13, t_6_1_1/38): ответ 0 при ненулевом
                               ; подынтегральном невозможен, это тот же вложенный отказ, только невидимый.
                               (and (number? ans) (= ans 0) (not (equal? ne 0))))
                          ; unknown/unintegrable внутри суммы/произведения правой части (и complex-infi —
                          ; деление на ноль) ответом это быть не может (int-check пропускал `F + unknown`, d/dx = F').
                          ; Как и провал int-check — пробуем следующий кандидат (поведение до RUBI.S1).
                          (rubi-note-reason 'nested-unknown)
                          (if *rubi-chk-trace* (set! *rubi-chk-log* (cons (list id ans ne 'tainted) *rubi-chk-log*)))
                          (rubi-bt-fallback ne id (and (pair? (cdr cands)) (nth (car (cdr cands)) 1)))
                          (if *rubi-trace* (rubi-trace-add (list 'rhs-fail id 'tainted ne)))
                          (hash-set! heads id #t)
                          (rubi-loop* (cdr cands) ne orig x heads xc exps))
                         ((and (not (equal? ans 'unknown))
                               (not (equal? ans 'unintegrable))
                               (not (equal? ans 'rubi-no-rule))
                               (not (equal? ans 'rubi-eval-error)))
                          (let* ((tc (and *rubi-prof* (clock-us)))
                                 ; RUBI.SYM.4: Log[E] в правой части — та же единица, что и в условии
                                 ; (см. rubi-log): без свёртки ответ правила содержал (^ (log E) -1),
                                 ; d/dx его не сходился с входом, и верное правило отвергалось
                                 ; (∫exp(asinh x): 7.1.6 #15 → 6.7.7 #43, ответ с log E).
                                 (ans-f (let ((fl (rubi-fold-log-e ans)))
                                          (if (equal? fl ans) ans (simplify fl))))
                                 ; RUBI.CH3.2: E правой части — символ (rubi-num-exp), а вход верхнего уровня записан exp(..):
                                 ; сверять с ним ответ, где E — параметр (1,7), нельзя; E возвращается к exp, если E нет в orig
                                 (ans-c (if (contains-sym? orig 'E) ans-f (rubi-restore-e ans-f)))
                                 (ok (rubi-int-check-search (if (rubi-has-ell? ans-c) (rubi-ell-convert ans-c) ans-c) orig x)))
                            (if tc
                                (begin (set! *rubi-p-check* (+ *rubi-p-check* (- (clock-us) tc)))
                                       (set! *rubi-p-checks* (+ *rubi-p-checks* 1))))
                            (if ok
                                (begin (rubi-bt-win ne id)
                                       (if *rubi-trace* (rubi-trace-add (list 'fire id ne *rubi-depth* binds)))
                                       ans-f)
                                (begin (rubi-bt-fallback ne id (and (pair? (cdr cands)) (nth (car (cdr cands)) 1)))
                                       (if *rubi-chk-trace* (set! *rubi-chk-log* (cons (list id ans ne) *rubi-chk-log*)))
                                       (if *rubi-trace* (rubi-trace-add (list 'rhs-fail id 'check ne)))
                                       (hash-set! heads id #t)
                                       (rubi-loop* (cdr cands) ne orig x heads xc exps)))))
                         ; «Первое правило окончательное» (флаг): unknown вложенного Int — окончательный.
                         ; По умолчанию — старое поведение: пробуем следующий кандидат.
                         ; RUBI.C11.2: если правило совпало только групповой привязкой (grouped), неизвестность
                         ; не окончательна и при флаге — совпадение «формально», следующее правило файла может
                         ; дать ответ (4.1.7/454, 4.1.7/466, 1.2.1.6/52).
                         ((equal? ans 'unknown)
                          (if *rubi-trace* (rubi-trace-add (list 'rhs-fail id 'unknown ne)))
                          (if (and *rubi-first-rule-final* (not grouped))
                              'unknown
                              (begin (rubi-bt-fallback ne id (and (pair? (cdr cands)) (nth (car (cdr cands)) 1)))
                                     (rubi-loop* (cdr cands) ne orig x heads xc exps))))
                         (#t (begin (rubi-bt-fallback ne id (and (pair? (cdr cands)) (nth (car (cdr cands)) 1)))
                                    (if *rubi-trace*
                                        (rubi-trace-add (list 'rhs-fail id
                                                              (if (equal? ans 'rubi-eval-error)
                                                                  (list 'error (substring *rubi-trace-err* 0 (min 70 (string-length *rubi-trace-err*))))
                                                                  ans)
                                                              ne)))
                                    (hash-set! heads id #t)
                                      (rubi-loop* (cdr cands) ne orig x heads xc exps))))))))))))

; RUBI.J3: int-check проверяет в точках x = 0.3 ... 2.2 и параметрах 1.1 ... 3.1; AppellF1 вне единичного круга
; (|b x/a| > 1) eval-num не считает (оставляет форму невычисленной - 'skip), и верный ответ с AppellF1 (1.1.1.2 #39, 1.1.3.3 #61:
; x AppellF1[1,-p,-q,2,-b x/a,-d x/c]) отвергался (1.1.1.2 #39 - первое по частоте «check», 71 задача). Запасная проверка
; ТОЛЬКО для ответов с appell-f1: тот же численный критерий (невязка производной <= 1e-7 (1 + |e|), не менее двух вычислимых
; точек) в точках x = 0.05 ... 0.2, где аргументы AppellF1 внутри круга для отношений параметров до ~ 3.
(define rubi-hyp-points '(1/20 1/10 3/20 1/5 1/4))
(define (rubi-has-head? e h)
  (cond ((not (pair? e)) #f)
        ((equal? (car e) h) #t)
        (else (any? (lambda (a) (rubi-has-head? a h)) (cdr e)))))
; RUBI.K: Hypergeometric2F1 вне единичного круга eval-num не считает; ответы вида (c+d x)^(n+1) 2F1[1,n+1,n+2,1+d x/c]
; (∫(a+b x)^n/x) с положительными параметрами int-check всегда имеют |аргумент| > 1 -> 'skip -> отказ. Запасная проверка
; только для ответов с hypergeometric-2f1: параметры берутся из тех же чисел, но знаки меняются (все +, каждый по одному -,
; все -); проверка ПРИНИМАЕТ при >= 1 раскладке 'ok и ни одной 'bad (раскладки 'skip пропускаются); точки x = 0.05 ... 0.25.
(define (rubi-sign-patterns k)
  (cons (map (lambda (i) 1) (range k))
        (cons (map (lambda (i) -1) (range k))
              (if (<= k 1) '()
                  (map (lambda (i) (map (lambda (j) (if (= i j) -1 1)) (range k))) (range k))))))
(define (rubi-2f1-check f e x)
  (let* ((e1 (simplify e))
         (ps (integrate::int-symbols (list '+ f e1) x))
         (stats (map (lambda (sg)
                       (let* ((vals (map2 list ps (map2 * sg integrate::int-test-params)))
                              (sub (lambda (u) (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr))) u vals)))
                              (f2 (sub f)) (e2 (sub e1)))
                         (try (integrate::int-numeric-status-at (list '- (integrate::int-diff x f2) e2) e2 x 0.0000001 rubi-hyp-points)
                              (lambda (err) 'skip))))
                     (rubi-sign-patterns (length ps)))))
    (and (member? 'ok stats) (not (member? 'bad stats)))))
; RUBI.2F1: запасная проверка ответов с ₂F₁/F₁ при ПСЕВДОСЛУЧАЙНЫХ параметрах. Прежние проверки берут одни и те же
; положительные параметры (1,7; 2,3; …) — аргументы F₁ (−d(a+bx)/(bc−ad), −f(a+bx)/(be−af)) при них то на разрезе [1,∞),
; то вне круга сходимости, и eval-num отказывает (skip:heads). Здесь параметры — детерминированный набор десятых долей
; со знаками (кратные 5 исключены: целые и полуцелые дают вырожденные ₂F₁); производная берётся один раз символьно.
; Принято: нет ни одного набора с невязкой (bad) среди <= 14 наборов и не меньше 3 наборов, где невязка мала в >= 2 точках
; (int-numeric-status-at, допуск 1e-7·(1+|e|)). Ответ, верный лишь при условиях на параметры, на «плохих» наборах даёт bad
; и отвергается (потеря, а не ложный ответ); неверный — bad на первом же наборе.
(define rubi-hyp2-xs '(1/20 1/10 3/20 1/5 1/4 3/10 2/5 1/2))
(define (rubi-hyp2-val i j)
  (let* ((s (modulo (+ 12345 (* 1103515245 (+ (* 31 i) (* 7919 j) 17))) 2147483648))
         (k (+ 3 (modulo (quotient s 65536) 37)))
         (k2 (if (= (modulo k 5) 0) (+ k 1) k))
         (sg (if (= (modulo (quotient s 1024) 2) 0) 1 -1)))
    (/ (* sg k2) 10)))
(define (rubi-hyp2-check f e x)
  (let* ((e1 (simplify e))
         (ps (integrate::int-symbols (list '+ f e1) x))
         (df (list '- (integrate::int-diff x f) e1)))
    (let loop ((j 0) (oks 0))
      (cond ((>= oks 3) #t)
            ((>= j 14) #f)
            (else
             (let* ((vals2 (let numbered ((rest ps) (i 0) (acc '()))
                             (if (null? rest) (reverse acc)
                                 (numbered (cdr rest) (+ i 1) (cons (list (car rest) (rubi-hyp2-val i j)) acc)))))
                    (sub (lambda (u) (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr))) u vals2)))
                    (e2 (sub e1))
                    (st (try (integrate::int-numeric-status-at (sub df) e2 x 0.0000001 rubi-hyp2-xs)
                             (lambda (err) 'skip))))
               (cond ((equal? st 'bad) #f)
                     ((equal? st 'ok) (loop (+ j 1) (+ oks 1)))
                     (else (loop (+ j 1) oks)))))))))
(define (rubi-hyp2-fallback f e x)
  (and (or (rubi-has-head? f 'appell-f1) (rubi-has-head? f 'hypergeometric-2f1))
       (try (rubi-hyp2-check f e x) (lambda (err) #f))))
; RUBI.CASE.2.5: финальная приёмка ответа Rubi. Поиск уже принимает ₂F₁/F₁
; запасной численной проверкой rubi-hyp2-fallback; здесь она повторяется,
; иначе верный ответ с аргументом ₂F₁ вне единичного круга отвергается
; стандартными параметрами int-check-F-final-ok?.
(define (rubi-final-check-ok? f e x)
  (or (integrate::int-check-F-final-ok? f e x)
      (try (rubi-hyp2-fallback f e x) (lambda (err) #f))))
(define (rubi-int-check f e x)
  (if *rubi-prof*
      (let ((how (try (int-check-rubi-how f e x) (lambda (err) 'err))))
        (hash-set! *rubi-chk-how* how (+ 1 (hash-ref *rubi-chk-how* how 0)))
        (or (equal? how 'simplify) (equal? how 'together) (equal? how 'numeric)
            (and (rubi-has-head? f 'appell-f1)
                 (let ((e1 (simplify e)))
                   (equal? (try (integrate::int-numeric-status-at (list '- (integrate::int-diff x f) e1) e1 x 0.0000001 rubi-hyp-points)
                                (lambda (err) 'skip))
                           'ok)))
            (and (rubi-has-head? f 'hypergeometric-2f1)
                 (try (rubi-2f1-check f e x) (lambda (err) #f)))
            (rubi-hyp-exp-check f e x)
            (rubi-hyp2-fallback f e x)))
      (or (int-check-rubi f e x)
          (and (rubi-has-head? f 'appell-f1)
               (let ((e1 (simplify e)))
                 (equal? (try (integrate::int-numeric-status-at (list '- (integrate::int-diff x f) e1) e1 x 0.0000001 rubi-hyp-points)
                              (lambda (err) 'skip))
                         'ok)))
          (and (rubi-has-head? f 'hypergeometric-2f1)
               (try (rubi-2f1-check f e x) (lambda (err) #f)))
          (rubi-hyp-exp-check f e x)
          (rubi-hyp2-fallback f e x))))

; RUBI.SYM.4: подынтегральное с гиперболическими головами сверяется ещё и в экспоненциальной записи.
; Cosh[u] = (E^u + E^-u)/2, Sinh[u] = (E^u - E^-u)/2 — тождество, которого simplify порта не знает: ответ
; правила 6.7.7 #43 (Int[ExpandTrigToExp[...]]) верный, но d/dx ответа формально не сходился с исходным
; E^x cosh x, и правило отвергалось (∫exp x cosh x, ∫exp(asinh x) через 7.1.6 #15).
(define (rubi-hyp-exp-check f e x)
  (and (pair? e) (rubi-hyp-head? e)
       (let ((e2 (try (expand (rubi-trig-to-exp e)) (lambda (err) #f))))
         (and e2 (not (equal? e2 e)) (rubi-int-check-search-1 f e2 x)))))

; INT.NUMCHK: та же проверка для ПОИСКА — без численной проверки самого F (она стоит десятки eval-num на
; кандидата: на срезе 1.1 в цикле это −43 задачи и +15 % времени). Проверка F выполняется на финальной
; приёмке ответа (rubi-integrate*), т.е. каждый выданный ответ ею всё равно покрыт.
; RUBI.CH3: условия, записанные численными вычислителями при проверке КАНДИДАТА (ряд 2F1 при z = 1 расходится и т. п.),
; к ответу не относятся — канал условий проверка не меняет (иначе li(x) получал чужое условие «Гаусс: Re(c−a−b) > 0»)
(define (rubi-int-check-search f e x)
  (car (capture-conditions (lambda ()
    (or (rubi-int-check-search-1 f e x)
        ; RUBI.SYM.4: под единой формой E — символ, а int-diff/simplify порта понимают (exp u);
        ; ответ и вход сверяются в записи exp, если в входе есть E (см. REPORT-RUBI-SYM4.md).
        (and (contains-sym? e 'E)
             (let ((f2 (rubi-restore-e f)) (e2 (rubi-restore-e e)))
               (and (not (equal? e2 e)) (rubi-int-check-search-1 f2 e2 x)))))))))
(define (rubi-int-check-search-1 f e x)
  (let ((how (try (integrate::int-check-rubi-formal f e x) (lambda (err) 'err))))
    (if *rubi-prof* (hash-set! *rubi-chk-how* how (+ 1 (hash-ref *rubi-chk-how* how 0))))
    (or (equal? how 'simplify) (equal? how 'together) (equal? how 'numeric)
        (and (rubi-has-head? f 'appell-f1)
             (let ((e1 (simplify e)))
               (equal? (try (integrate::int-numeric-status-at (list '- (integrate::int-diff x f) e1) e1 x 0.0000001 rubi-hyp-points)
                            (lambda (err) 'skip))
                       'ok)))
        (and (rubi-has-head? f 'hypergeometric-2f1)
             (try (rubi-2f1-check f e x) (lambda (err) #f)))
        (rubi-hyp-exp-check f e x)
        (rubi-hyp2-fallback f e x))))

; Ответ, в котором где-либо есть метка отказа (unknown вложенного Int, unintegrable), — не ответ.
; int-check такого не отвергал: символ-метка для int-diff — константа, и слагаемое `+ unknown` или
; множитель `0·unknown` проходили проверку.
(define (rubi-tainted? e)
  (cond ((symbol? e) (or (equal? e 'unknown) (equal? e 'unintegrable) (equal? e 'rubi-no-rule)))
        ((pair? e) (any? rubi-tainted? e))
        (else #f)))

; Вход из математического языка (integrate_rubi): отказ — невычисленная форма integrate, как у integrate,
; иначе статус ответа JSON/MCP принимал голый символ unknown за answer (pretty = "unknown").
(define (rubi-integrate-form e x)
  (let ((r (rubi-integrate e x)))
    (if (equal? r 'unknown) (list 'integrate e x) r)))

; RUBI.NORULE: запись корня в ответе. В .m-правилах Sqrt[Pi] (генератор пишет (sqrt pi)), а остальной порт
; (risch-special, integrate) записывает корень степенью 1/2 — без канонизации один и тот же интеграл (∫e^(x²),
; 2.3 #11, ответ содержит Sqrt[Pi]) получал две разные записи в зависимости от пути решения. Канонизируется
; только корень атома (pi, 2, E): √(1/2·pi) и √(2/pi) в ответах Френеля остаются как есть (их так и ждут).
(define (rubi-sqrt-atom-to-pow e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'sqrt) (equal? (length e) 2) (not (pair? (cadr e))))
         (list '^ (cadr e) 1/2))
        ((equal? (car e) 'quote) e)
        (else (cons (car e) (map rubi-sqrt-atom-to-pow (cdr e))))))
; RUBI.S16: E, появившееся при нормализации голов (exp u -> E^u, rubi-normalize-heads), возвращается к exp:
; int-check считает свободный символ E параметром (значение 1,7), и ответ ∫pi/sqrt(16 - exp(2)) = (* ... x) с E^2
; не проходил проверку против входа с (exp 2) - 2,6 с в проверке и отказ. Если E есть во входе (параметр) - не трогаем.
; RUBI.CH8: правые части пишут постоянную e как (exp 1) и при вычислении получают float 2.718281828459045 (8.1 #3:
; ∫erfi = x·erfi − e^(x²)/√π, ответ шёл с (^ 2.718... (^ x 2))) — float e тоже возвращается к exp.
(define rubi-float-e 2.718281828459045)
; RUBI.NF.2: Log[E] = 1 (автовычисление Mathematica). В правых частях Rubi пишет Log[F] при F = E —
; без этой свёртки единая форма давала ответы Ei(x·log E), erfi(x·√log E): simplify log E не сворачивает.
; Сворачиваем в ГОТОВОМ ответе (а не при вычислении правой части): правка rubi-num-log меняла форму
; промежуточных подзадач и роняла e^(asinh x) в бюджет поиска.
(define (rubi-fold-log-e u)
  (cond ((not (pair? u)) u)
        ((and (equal? (car u) 'log) (= (length u) 2) (equal? (cadr u) 'E)) 1)
        (else (map rubi-fold-log-e u))))

(define (rubi-restore-e r)
  (cond ((equal? r 'E) '(exp 1))
        ((and (number? r) (not (integer? r)) (equal? r rubi-float-e)) '(exp 1))
        ((not (pair? r)) r)
        ; (sqrt pi) из правых частей (erf, Fresnel…) и (^ pi 1/2) из definite — разные записи, simplify их не сводит
        ((equal? r '(sqrt pi)) '(^ pi 1/2))
        ((and (equal? (car r) '^) (= (length r) 3) (or (equal? (cadr r) 'E) (equal? (cadr r) rubi-float-e)))
         (list 'exp (rubi-restore-e (caddr r))))
        (else (map rubi-restore-e r))))

; RUBI.S16: ВЕСЬ вызов (simplify входа, поиск, simplify и int-check ответа) укладывается в один бюджет;
; раньше simplify/int-check после поиска шли вне лимита (int-check ложного ответа - до секунд) и стенд убивал
; задачу на 5 с. Поиск получает бюджет минус запас на обработку ответа; не уложились - unknown.
(define rubi-post-reserve 0.4)
(define (rubi-integrate e x)
  (let ((t0 (clock-us)))
    ; RUBI.SYM.3: форма выставляется до rubi-ensure — индекс правил строится уже в ней
    (rubi-form-sync)
    (rubi-ensure)
    (let ((loaded #t))
      (if (not loaded)
          (rubi-fail 'load)
          ; загрузка правил входит в бюджет вызова: стенд убивает процесс по общему времени задачи
          (let* ((budget (max 1.0 (- rubi-time-limit (/ (- (clock-us) t0) 1000000.0))))
                 (rr (call-with-time-limit
                      budget
                      (lambda () (rubi-integrate* e x (max (* 0.5 budget) (- budget rubi-post-reserve)))))))
            (set! match::ac-id-skip #f)
            (if (and (pair? rr) (equal? (car rr) 'ok))
                (cadr rr)
                (rubi-fail 'budget)))))))

; Запасная ступень integrate: rubi-integrate со своим бюджетом limit (с); прежний бюджет восстанавливается.
; Отказ — #f (не unknown): вызывающему достаточно проверки на ложь.
(define (rubi-integrate-within e x limit)
  (let ((old rubi-time-limit))
    (unwind-protect
      (begin (set! rubi-time-limit limit)
             (let ((r (rubi-integrate e x)))
               (if (equal? r 'unknown) #f r)))
      (set! rubi-time-limit old))))

; RUBI.D5: решение с журналом одной строкой для JSON-хоста (пилот с журналом в qedra-bench, вход rubi_trace).
; input - строка входного языка, var - имя переменной (строка), limit - бюджет движка, с. Возвращает строку без
; id задачи: первая строка «T<TAB>verdict<TAB>мс<TAB>попыток<TAB>причина», далее «R<TAB>запись журнала» (~s) в
; хронологическом порядке - формат tools/rubi/diagnose-run.lisp без первой колонки id. Флаги и бюджет
; восстанавливаются, журнал очищается (воркер стенда долгоживущий).
(define (rubi-trace-run input var limit)
  (let ((e (try (math-read input) (lambda (err) #f)))
        (old-limit rubi-time-limit)
        (old-trace *rubi-trace*))
    (if (not e)
        "T\tparse-error\t0\t0\t-"
        (begin
          (set! rubi-time-limit limit)
          (set! *rubi-trace* #t)
          (let* ((t0 (clock-us))
                 (r (try (rubi-integrate e (string->symbol var)) (lambda (err) 'unknown)))
                 (ms (quotient (- (clock-us) t0) 1000))
                 (head (string-append "T\t" (if (equal? r 'unknown) "unknown" "ok") "\t" (to-string ms) "\t"
                                      (to-string *rubi-tries*) "\t" (to-string *rubi-last-reason*)))
                 (recs (map (lambda (rec) (string-append "R\t" (format "~s" rec))) (reverse *rubi-trace-log*))))
            (set! rubi-time-limit old-limit)
            (set! *rubi-trace* old-trace)
            (set! *rubi-trace-log* '())
            (string-join (cons head recs) (format "~%")))))))

; RUBI.CH-C0c: нормализация входа — simplify + DeactivateTrig + UnifyInertTrigFunction (ред. C0c.4).
; Подробности — REPORT-RUBI-C0C.md; маскировка инертных голов живёт в lib/rubi/utils.lisp
; (rubi-inert-mask/unmask) и по умолчанию выключена — см. комментарий у *rubi-inert-mask*.
; RUBI.CH4.3: rubi-inert-heads-of/-list и rubi-unique-inert переехали в utils.lisp (нужны и
; FixInertTrigFunction); в этом файле остаются только проверки формы для нормализации входа.
; в выражении больше одной различной тригонометрической головы?

(define (rubi-inert-multi-heads? u)
  (let ((hs (rubi-inert-heads-of u)))
    (and (pair? hs) (pair? (cdr hs)))))
; моном по одной тригонометрической голове: множители без тригонометрии (числа, параметры, полиномы по x),
; голая голова (trig arg) с аргументом без тригонометрии и её степень, произведение таких множителей.
; Именно для этих форм в исходнике есть клаузы UnifyInertTrigFunction (IUF.m:6549-6565: u_^n_. с
; тригонометрической головой). Вложенные структуры не унифицируем — правила порта 4.1/4.2 записаны для
; cos-формы (регрессия: sqrt(a*cos(x)^2) — master 72 мс, с унификацией упиралось в бюджет).
(define (rubi-inert-all-monomials? fs)
  (or (null? fs) (and (rubi-inert-monomial? (car fs)) (rubi-inert-all-monomials? (cdr fs)))))
; база степени: (b*cos(x))^(3/2) годится (произведение голых голов), а (a*cos(x)^2)^(1/2) — нет:
; степень cos внутри радикала после унификации не сопоставляется ни одним правилом 4.1/4.2
(define (rubi-inert-base-ok? b)
  (cond ((not (pair? b)) #t)
        ((null? (rubi-inert-heads-of b)) #t)
        ((member? (car b) (rubi-trig-heads))
         (and (pair? (cdr b)) (null? (rubi-inert-heads-of (cadr b)))))
        ((equal? (car b) '*) (rubi-inert-all-bases? (cdr b)))
        ((equal? (car b) '+) (rubi-inert-all-monomials? (cdr b)))
        (else #f)))
(define (rubi-inert-all-bases? bs)
  (or (null? bs) (and (rubi-inert-base-ok? (car bs)) (rubi-inert-all-bases? (cdr bs)))))
(define (rubi-inert-monomial? u)
  (cond ((not (pair? u)) #t)
        ((null? (rubi-inert-heads-of u)) #t)       ; нет тригонометрии — множитель/слагаемое как есть
        ((member? (car u) (rubi-trig-heads))
         (and (pair? (cdr u)) (null? (rubi-inert-heads-of (cadr u)))))
        ((equal? (car u) '*) (rubi-inert-all-monomials? (cdr u)))
        ((equal? (car u) '+) (rubi-inert-all-monomials? (cdr u)))
        ((equal? (car u) '^) (and (= (length u) 3) (rubi-inert-base-ok? (cadr u))))
        (else #f)))
; Маскировка инертных голов (rubi-inert-mask в utils.lisp) — эксперимент шага 2: выигрыша не даёт, а теряет
; задачи, где правила порта рассчитаны на активированную форму (sec^2 -> cos^-2 и т.п.): на наборе 4.2-4.6
; 39/56 против 45/56 при выключенной маскировке, плюс потери sec^2/sec^4/csc^2 в 4.5/4.6. Поэтому выключена;
; понадобится при переносе клауз IUF.m:6566-7361 (произведения двух инертных голов).
(define *rubi-inert-mask* #f)
(define *rubi-inert-unify* #t)
; RUBI.CH567.3: оставлять тригонометрию мнимого аргумента без нормализации Unify (см. rubi-inert-normalize-trig).
; #t — поведение по умолчанию (как было); #f — нормализовать и её (замер «до/после»).
(define *rubi-inert-imag* #t)
; RUBI.CH4.5: отрицательная степень тригонометрической головы внутри суммы. В порте heads
; sec/csc/tan/cot живут как отрицательные степени sin/cos (ac-norm: sec^2 -> cos^-2), а клаузы
; Unify/DeactivateTrig исходника записаны для инертных голов как отдельных имён: (a+b Cos[v])^n
; (6588-6590), (a+b (c Cos[v])^n)^p (6798-6800) — там Cos стоит БЕЗ степени. Переписывание
; cos^-2 как «cos-суммы» даёт sin[x+Pi/2]^-2 и убивает sec-форму правила 4.5.7 #9 (регрессия
; sqrt(a+b sec^2), база 5f4e465), поэтому такие суммы не нормализуем; произведения голов —
; по-прежнему нормализуем (6601-6612 и т. п.).
(define (rubi-inert-neg-trig-power? u)
  (cond ((not (pair? u)) #f)
        ((and (equal? (car u) '^) (= (length u) 3) (number? (caddr u)) (< (caddr u) 0)
              (pair? (cadr u)) (member? (car (cadr u)) '(sin cos)))
         #t)
        (else (any? rubi-inert-neg-trig-power? (cdr u)))))
(define (rubi-inert-neg-trig-power-in-sum? u)
  (cond ((not (pair? u)) #f)
        ((and (equal? (car u) '+) (any? rubi-inert-neg-trig-power? (cdr u))) #t)
        (else (any? rubi-inert-neg-trig-power-in-sum? (cdr u)))))
(define (rubi-simplify-inert e x)
  (if *rubi-prof*
      (let ((t0 (clock-us)))
        (let ((r (rubi-simplify-inert-1 e x)))
          (set! *rubi-p-inert* (+ *rubi-p-inert* (- (clock-us) t0)))
          r))
      (rubi-simplify-inert-1 e x)))
(define (rubi-simplify-inert-1 e x)
  (if *rubi-nf*
      ; RUBI.NF: автовычисление Mathematica не делает тригонометрических тождеств — ни общего simplify
      ; (tan → sin/cos), ни DeactivateTrig/Fix/Unify на входе. Мост к инертной форме остаётся хвостовым
      ; правилом 4.1.0.1 #1 (rubi-deactivate-trig), как в исходнике.
      (rubi-nf e)
      (let* ((m (if *rubi-inert-mask* (rubi-inert-mask e x) (list e '())))
             (u (rubi-inert-unmask (simplify (car m)) (cadr m)))
             (v (if (not *rubi-inert-unify*) u (rubi-inert-normalize-trig u x))))
        (if *rubi-prof* (set! *rubi-p-inertn* (+ *rubi-p-inertn* 1)))
        v)))
; Роль DeactivateTrig (IUF.m:6194-6195) в порте: фаза аргумента (DeactivateTrigAux, 6198-6219), затем
; FixInertTrigFunction (6228-6484) и UnifyInertTrigFunction (6549-7362). Этой же функцией пользуется правило
; 4.1.0.1 #1 (utils.lisp: rubi-deactivate-trig), поэтому повторный вызов её не меняет — самовызова нет.
; Условия формы (C0c) — ниже: голый sin/cos, произведения двух голов, вложенные структуры и мнимый аргумент
; остаются как есть, потому что правила порта записаны для этих форм.
(define (rubi-inert-normalize-trig u x)
  (let ((v (rubi-deactivate-trig-aux u x)))
    (if (or (and (pair? v) (member? (car v) '(sin cos)) (null? (cddr v)))
            ; RUBI.CH4.4: произведения голов, к которым применима клауза Unify (IUF.m:6566-7361),
            ; нормализуются и при нескольких головах — за это и отвечает rubi-inert-unify-able?
            (and (rubi-inert-multi-heads? v) (not (rubi-inert-unify-able? v x)))
            (and (not (rubi-inert-monomial? v)) (not (rubi-inert-unify-able? v x)))
            ; RUBI.CH4.5: sec/csc/tan/cot в порте — отрицательные степени sin/cos; «cos-сумма»
            ; из них не унифицируется, если это не произведение голов (см. ниже): иначе теряется
            ; sec-форма правила 4.5.7 #9
            (and (rubi-inert-neg-trig-power-in-sum? v) (not (rubi-inert-unify-able? v x)))
            ; RUBI.HYP: форма после гиперболических клауз DeactivateTrigAux (IUF.m:6210-6218) —
            ; тригонометрия мнимого аргумента; cos[I v] -> sin[I v + Pi/2] (IUF.m:6588-6590) её
            ; ломает (обратный переход к sinh/cosh в rubi-hyp-from-imag ждёт мнимый аргумент).
            ; RUBI.CH567.3: флаг — для сравнения «с нормализацией мнимого аргумента» (см. замер в
            ; research/rubi/ch567-tainted.md): гипотеза — без нормализации правила глав 2.x (индекс
            ; записан в sin-форме) не видят cos[I v]^n и задача умирает.
            (and *rubi-inert-imag* (contains-sym? v '%i)))
        v
        ; RUBI.CH4.3: порядок исходника — сначала FixInertTrigFunction (6228-6484), затем Unify (6549+)
        (rubi-unify-inert-trig-function (rubi-fix-inert-trig-function v x) x))))


; RUBI.D2: нормализованный вход задачи (как его видит rubi-int) - для форм корпуса в диагностике
(define (rubi-norm-form e)
  (let ((e0 (rubi-simplify-inert e 'x)))
    (rubi-group-free
     (rubi-norm-input e0 'x)
     'x)))

(define (rubi-integrate* e x budget)
  (let* ((xx 'x)
         ; RUBI.CH8: головы входа — как в образцах и ответах (LambertW → lambert_w …); и финальная приёмка сверяет
         ; ответ с этим же входом (иначе неизвестная голова LambertW делает приёмку невозможной)
         (e (rubi-rename-heads e *rubi-head-alias-in*))
         (e0 (rubi-simplify-inert e x))
         ; правила Rubi записаны для переменной x; чтобы переменная интегрирования не слилась
         ; с параметром x (∫x·y dy), параметр x получает свежий символ, которого нет в выражении
         (collide (and (not (equal? x xx)) (contains-sym? e0 xx)))
         (fresh (and collide (rubi-fresh-sym e0 "x")))
         (ee (cond ((equal? x xx) e0)
                   (collide (rubi-rename e0 (list (cons xx fresh) (cons x xx))))
                   (else (rubi-rename e0 (list (cons x xx))))))
         (back (cond ((equal? x xx) '())
                     (collide (list (cons fresh xx) (cons xx x)))
                     (else (list (cons xx x)))))
         (_skip (set! match::ac-id-skip #t))
         ; RUBI.NF: единая форма — ac-norm не переписывает csc/cot/sec в степени sin/tan/cos
         (_ (rubi-form-sync))
         (rr (call-with-time-limit
              budget
              (lambda ()
                (set! *rubi-depth* 0)
                (set! *rubi-stack* '())
                (set! *rubi-failed* (make-hash))
                (set! *rubi-cands* (make-hash))
                (set! *rubi-cands2* (make-hash))
                (set! rubi::*rubi-polyq-cache* (make-hash))
                (set! rubi::*rubi-polyq-full-cache* (make-hash))
                (set! rubi::*rubi-expand-cache* (make-hash))
                (set! rubi::*rubi-zero-cache* (make-hash))
                (set! rubi::*rubi-posq-cache* (make-hash))
                (set! rubi::*rubi-deact-cache* (make-hash))
                (set! *rubi-gw-seen* (make-hash))
                (set! *rubi-active* (make-hash))
                (set! *rubi-memo* (make-hash))
                (set! *rubi-fail-reasons* '())
                (if *rubi-trace* (rubi-trace-reset))
                (set! rubi::*rubi-stub-calls* (make-hash))
                (set! *rubi-errors* (make-hash))
                ; счётчик попыток — на задачу, а не на процесс (воркер стенда долгоживущий)
                (set! *rubi-tries* 0)
                (rubi-bt-reset)
                (rubi-int ee ee xx)))))
    (set! match::ac-id-skip #f)
    (if (not (and (pair? rr) (equal? (car rr) 'ok)))
        (rubi-fail 'budget)
        (let ((r (cadr rr)))
          (cond ((equal? r 'unknown) 'unknown)
                ((rubi-tainted? r) (rubi-fail 'tainted))
                (else
                 ; RUBI.NF.2: под единой формой вход приходит как (^ E u), поэтому E в ответе разворачивается
                 ; всегда (иначе наружу уходили Ei(1+x)/E и т. п.); без флага — прежнее условие, иначе
                 ; ответы вида exp(asinh(x)) теряли форму и проверка упиралась в бюджет.
                 (let* ((raw (let ((r1 (rubi-fold-log-e (if (or *rubi-nf* (not (contains-sym? e0 'E)))
                                                          (rubi-restore-e r)
                                                          r))))
                               (if (rubi-has-ell? r1) (rubi-ell-convert r1) r1)))
                        ; RUBI.HYP: гиперболические входы Rubi сводит к тригонометрии мнимого аргумента
                        ; (IUF.m:6210-6218); обратно — как Simplify Математики на ответе.
                        (r2 (simplify (rubi-hyp-from-imag (rubi-sqrt-atom-to-pow (rubi-rename raw back))))))
                   ; RUBI.SPEED: ответ уже проверен int-check в rubi-loop* — против того же ee = simplify(e)
                   ; (переменную не переименовывали), — и при восстановлении E/эллиптики и simplify не изменился.
                   ; Вторая проверка того же сравнения время только тратит (на ok-sample — целая проверка на задачу).
                   ; INT.NUMCHK: финальная приёмка — ещё и численная производная самого ответа (ветви √(u²) и
                   ; √(−a)√(−b) проходили формальную проверку); одна проверка на задачу, поиск не затронут.
                   ; RUBI.SYM.4: если ответ развёрнут из E в exp (условие выше), сверять его надо с входом в
                   ; ТОЙ ЖЕ записи — иначе (^ E (* 2 x)) не сходится с (* 1/2 (exp (* 2 x))): ∫E^x*E^x и
                   ; ∫exp(asinh x) отвергались как «другая форма», хотя ответ верный.
                   ; RUBI.SYM.4: под единой формой ответ разворачивается из E в exp (см. выше), поэтому и вход
                   ; для сверки берётся в той же записи: иначе (^ E (* 2 x)) не сходится с (* 1/2 (exp (* 2 x)))
                   ; и готовый ответ отвергался как «другая форма» (∫E^x cosh x, ∫exp(asinh x)).
                   (let* ((ec (if *rubi-nf* (rubi-restore-e e) e))
                          (fast (and (null? back) (equal? r2 r)))
                          (f1 (or fast (rubi-int-check-search r2 ec x)))
                          (f2 (and f1 (car (capture-conditions (lambda () (rubi-final-check-ok? r2 (simplify ec) x)))))))
                     (if (and f1 f2)
                       ; TIDY.4: √u·√v → √c при числовом u·v, только при 'ok численной проверки свёрнутого (api.lisp)
                       (integrate::int-fold-sqrts-checked r2 (simplify e) x)
                       ; RUBI.CH567.2: диагностика финальной приёмки — какой её шаг отверг ответ
                       ; (form: формальная проверка поиска, F: численная производная самого ответа).
                       (begin
                         (if *rubi-chk-trace*
                             (set! *rubi-chk-log*
                                   (cons (list 'final r2 (simplify e) (if f1 'F-final (quote formal)))
                                         *rubi-chk-log*)))
                         (rubi-fail 'check)))))))))))
