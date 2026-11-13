; RUBI.CH-C.2: утилиты главы 4 в lib/rubi/utils-c.lisp (InertTrigFreeQ, FunctionOfTrigOfLinearQ).
; Источник: Rubi 4.17.3.0, commit 61e9c18, IntegrationUtilityFunctions.m (строки указаны в тестах).
; Файл утилит грузится движком перед правилами главы 4; здесь — явно, тест движок не поднимает.
(load "lib/rubi/utils-c.lisp")

(deftest "rubi-c: InertTrigFreeQ — тригонометрия есть"
  (assert-true (not (rubi::rubi-inert-trig-free-q '(sin x))))
  (assert-true (not (rubi::rubi-inert-trig-free-q '(* 2 (cos (+ a (* b x)))))))
  (assert-true (not (rubi::rubi-inert-trig-free-q '(+ 1 (tan x))))))

(deftest "rubi-c: InertTrigFreeQ — тригонометрии нет"
  (assert-true (rubi::rubi-inert-trig-free-q '(+ 1 x)))
  (assert-true (rubi::rubi-inert-trig-free-q '(* a (^ x 2))))
  (assert-true (rubi::rubi-inert-trig-free-q 'y)))

(deftest "rubi-c: FunctionOfTrigOfLinearQ — линейный аргумент"
  ; IUF.m:4358: (c+d*x)^m*(a+b*trig[e+f*x])^n
  (assert-true (rubi::rubi-function-of-trig-of-linear-q '(* (^ x 2) (sin (+ a (* b x)))) 'x))
  (assert-true (rubi::rubi-function-of-trig-of-linear-q '(+ 1 (^ (cos (* 2 x)) 2)) 'x))
  (assert-true (rubi::rubi-function-of-trig-of-linear-q '(/ (sin x) (cos x)) 'x)))

(deftest "rubi-c: FunctionOfTrigOfLinearQ — нелинейный аргумент или не тригонометрия"
  (assert-true (not (rubi::rubi-function-of-trig-of-linear-q '(sin (^ x 2)) 'x)))
  (assert-true (not (rubi::rubi-function-of-trig-of-linear-q (list '^ (list 'sin (list '^ 'x 2)) '(/ 1 2)) 'x)))
  (assert-true (not (rubi::rubi-function-of-trig-of-linear-q '(+ 1 x) 'x)))
  (assert-true (not (rubi::rubi-function-of-trig-of-linear-q '(exp x) 'x))))

(deftest "rubi-c: FunctionOfTrigOfLinearQ — параметр в аргументе и смешанные случаи"
  ; e+0*x — тоже линейный аргумент, поэтому sin(a+b) годится
  (assert-true (rubi::rubi-function-of-trig-of-linear-q '(sin (+ a b)) 'x))
  (assert-true (not (rubi::rubi-function-of-trig-of-linear-q '(* (sin x) (sin (* x x))) 'x))))

; ---------- RUBI.CH-C0b: общие утилиты IUF.m (InertTrigQ, Known*IntegrandQ, TrigSimplifyQ) ----------
; Источник: Rubi 4.17.3.0, commit 61e9c18, IntegrationUtilityFunctions.m; строки — в комментариях.
(load (string-append lib-dir "rubi/utils.lisp"))

(deftest "rubi-c: InertTrigQ — одна голова (IUF.m:6160)"
  (assert-true (and (rubi::rubi-inert-trig-q 'sin) (rubi::rubi-inert-trig-q 'cos)
                    (rubi::rubi-inert-trig-q 'tan) (rubi::rubi-inert-trig-q 'cot)
                    (rubi::rubi-inert-trig-q 'sec) (rubi::rubi-inert-trig-q 'csc)))
  ; в порте инертных голов нет: узел (sin x) — та же голова
  (assert-true (rubi::rubi-inert-trig-q '(sin x)))
  ; подделка: гиперболическое, обратное, произвольный символ
  (assert-true (not (rubi::rubi-inert-trig-q 'sinh)))
  (assert-true (not (rubi::rubi-inert-trig-q 'asin)))
  (assert-true (not (rubi::rubi-inert-trig-q 'x))))

(deftest "rubi-c: InertTrigQ — две и три головы (IUF.m:6162/6167, InertReciprocalQ 6170)"
  (assert-true (rubi::rubi-inert-trig-q 'sin 'sin))
  ; взаимно обратные — в любом порядке: sin/csc, cos/sec, tan/cot
  (assert-true (and (rubi::rubi-inert-trig-q 'sin 'csc) (rubi::rubi-inert-trig-q 'csc 'sin)))
  (assert-true (and (rubi::rubi-inert-trig-q 'cos 'sec) (rubi::rubi-inert-trig-q 'sec 'cos)))
  (assert-true (and (rubi::rubi-inert-trig-q 'tan 'cot) (rubi::rubi-inert-trig-q 'cot 'tan)))
  ; подделка: не пара и не совпадение; «обратная» не по той оси
  (assert-true (not (rubi::rubi-inert-trig-q 'sin 'cos)))
  (assert-true (not (rubi::rubi-inert-trig-q 'sin 'sec)))
  ; три головы: InertTrigQ[f,g] && InertTrigQ[g,h]
  (assert-true (rubi::rubi-inert-trig-q 'sin 'csc 'sin))
  (assert-true (not (rubi::rubi-inert-trig-q 'sin 'cos 'sin))))

(deftest "rubi-c: KnownTrigIntegrandQ — синус/косинус (IUF.m:7368, клаузы 7384-7391)"
  ; 7385: u === 1
  (assert-true (rubi::rubi-known-sine-integrand-q 1 'x))
  ; 7386: (a+b*sin(e+f x))^m
  (assert-true (rubi::rubi-known-sine-integrand-q '(^ (+ a (* b (sin (+ e (* f x))))) m) 'x))
  ; 7388/7389: A+C*sin(x)^2 и A+B*sin(x)+C*sin(x)^2
  (assert-true (rubi::rubi-known-sine-integrand-q '(+ A (* C (^ (sin x) 2))) 'x))
  (assert-true (rubi::rubi-known-sine-integrand-q '(+ A (* B (sin x)) (* C (^ (sin x) 2))) 'x))
  ; 7387/7390/7391: произведение степени двучлена на многочлен по ядру
  (assert-true (rubi::rubi-known-sine-integrand-q
                '(* (^ (+ a (* b (sin x))) m) (+ A (* B (sin x)))) 'x))
  (assert-true (rubi::rubi-known-sine-integrand-q
                '(* (^ (+ a (* b (cos x))) -2) (+ A (* C (^ (cos x) 2)))) 'x))
  ; подделки: нелинейный аргумент, коэффициент зависит от x, чужая голова
  (assert-true (not (rubi::rubi-known-sine-integrand-q '(sin (^ x 2)) 'x)))
  (assert-true (not (rubi::rubi-known-sine-integrand-q '(* x (sin x)) 'x)))
  (assert-true (not (rubi::rubi-known-sine-integrand-q '(tan x) 'x))))

(deftest "rubi-c: Known*IntegrandQ — tan/cot/sec/csc (IUF.m:7372/7376/7380)"
  (assert-true (rubi::rubi-known-tangent-integrand-q '(+ 1 (^ (tan x) 2)) 'x))
  (assert-true (rubi::rubi-known-tangent-integrand-q '(^ (+ a (* b (tan (+ e (* f x))))) 3) 'x))
  (assert-true (not (rubi::rubi-known-tangent-integrand-q '(^ (tan x) 3) 'x)))  ; степень 3 — не клауза
  (assert-true (not (rubi::rubi-known-tangent-integrand-q '(cot x) 'x)))
  (assert-true (rubi::rubi-known-cotangent-integrand-q '(+ a (* b (^ (cot (+ e (* f x))) 2))) 'x))
  (assert-true (not (rubi::rubi-known-cotangent-integrand-q '(tan x) 'x)))
  ; secant: головы sec и csc (7381)
  (assert-true (rubi::rubi-known-secant-integrand-q '(^ (sec x) 2) 'x))
  (assert-true (rubi::rubi-known-secant-integrand-q '(^ (csc x) 2) 'x))
  (assert-true (rubi::rubi-known-secant-integrand-q '(/ 1 (^ (+ 1 (* 2 (sec x))) 2)) 'x))
  (assert-true (not (rubi::rubi-known-secant-integrand-q '(cos x) 'x))))

(deftest "rubi-c: TrigSimplify — тождества (IUF.m:2740/2742/2744/2756/2762)"
  ; 2740: a cos²+a sin²+v -> a+v
  (assert-equal 1 (rubi::rubi-trig-simplify '(+ (^ (sin x) 2) (^ (cos x) 2))))
  (assert-equal 3 (rubi::rubi-trig-simplify '(+ 1 (* 2 (^ (sin x) 2)) (* 2 (^ (cos x) 2)))))
  ; 2742: a sec²−a tan²+v -> a+v
  (assert-equal 2 (rubi::rubi-trig-simplify '(+ 1 (^ (sec x) 2) (* -1 (^ (tan x) 2)))))
  ; 2756: u+v sin²+w при u=−v -> u cos²+w; 2762: u+v tan²+w при u=v -> u sec²+w
  (assert-equal '(^ (cos x) 2) (rubi::rubi-trig-simplify '(+ 1 (* -1 (^ (sin x) 2)))))
  (assert-equal '(^ (sec x) 2) (rubi::rubi-trig-simplify '(+ 1 (^ (tan x) 2))))
  ; снизу вверх: тождество срабатывает внутри произведения
  (assert-equal 3 (rubi::rubi-trig-simplify '(* 3 (+ (^ (sin x) 2) (^ (cos x) 2)))))
  ; подделка: разные аргументы и разные коэффициенты не складываются
  (assert-equal '(+ (^ (sin x) 2) (^ (cos (* 2 x)) 2))
                (rubi::rubi-trig-simplify '(+ (^ (sin x) 2) (^ (cos (* 2 x)) 2))))
  (assert-equal '(+ (^ (sin x) 2) (* 2 (^ (cos x) 2)))
                (rubi::rubi-trig-simplify '(+ (^ (sin x) 2) (* 2 (^ (cos x) 2))))))

(deftest "rubi-c: TrigSimplifyQ — меняет ли TrigSimplify (IUF.m:2703)"
  (assert-true (rubi::rubi-trig-simplify-q '(+ (^ (sin x) 2) (^ (cos x) 2))))
  (assert-true (rubi::rubi-trig-simplify-q '(+ 1 (^ (tan x) 2))))
  (assert-true (not (rubi::rubi-trig-simplify-q '(+ 1 x))))
  (assert-true (not (rubi::rubi-trig-simplify-q '(* 2 (sin x)))))
  (assert-true (not (rubi::rubi-trig-simplify-q '(^ (sin x) 2)))))
; ---------- RUBI.CH-C0c: регрессия C0b — TrigSimplifyQ на нетригонометрическом входе ----------
; Правило 4.7.5 #66 in Rubi: (TrigSimplifyQ[u]) → Int[TrigSimplify[u]]. Пока TrigSimplify звал simplify,
; TrigSimplifyQ был истинен почти для любого входа (simplify переупорядочивает произведение, например
; x·e^(atanh(a·x)) → e^(atanh(a·x))·x), правило срабатывало, уходило в тупик и ∫x·e^(atanh(a·x)) не брался
; (CI: INT.FIX2.e). TrigSimplify по исходнику (IUF.m:2708-2717, 2936) применяет только тригонометрические
; тождества и возвращает u как есть. Гиперболические головы в порте входят в rubi-trig-heads — их тоже не трогаем.

(deftest "rubi-c: TrigSimplifyQ ложен вне тригонометрических тождеств (регрессия C0b)"
  (for-each (lambda (e) (assert-true (not (rubi::rubi-trig-simplify-q e))))
            '((* x (^ E (atanh (* a x)))) (+ 1 x) (* 2 y) x (^ E (atanh x)) (sin x)
              (^ (tanh x) 2) (* x (cosh x)) (+ 1 (^ (sinh x) 2)))))

(deftest "rubi-c: TrigSimplify не переупорядочивает произведение и не раскрывает tan"
  (assert-equal '(* x (^ E (atanh (* a x)))) (rubi::rubi-trig-simplify '(* x (^ E (atanh (* a x))))))
  (assert-equal '(^ (tan x) 2) (rubi::rubi-trig-simplify '(^ (tan x) 2)))
  (assert-equal '(+ 1 (* a (cos x))) (rubi::rubi-trig-simplify '(+ 1 (* a (cos x))))))

; (c0c-ok? f) — движок Rubi даёт ответ, и производная ответа равна входу
(define (c0c-ok? f)
  (let ((F (rubi-integrate f 'x)))
    (and (pair? F) (not (equal? F 'unknown)) (int-check F f 'x))))

(deftest "rubi-c: e^(k·atanh(a·x)), e^(asinh(a·x)) — движок Rubi снова берёт (регрессия C0b)"
  ; RUBI.MATCH: интегралы с atanh берутся снова — правило 7.3.6 #2 порождает подзадачу с E во входе, а ложное
  ; совпадение 1.4.1 #42 (`E^(atanh(ax))` разбиралось как `(a_+b_. x^n_)^q` с a=E) подменяло проверяемый вход
  ; E-формой, и верный ответ отвергался. Показатель степени теперь не вырождается (`Power` не OneIdentity):
  ; см. ac-skippable? в lib/match.lisp и REPORT-RUBI-MATCH.md, «Глава 7».
  (assert-true (c0c-ok? (math-eval "exp(asinh(x))")))
  (assert-true (c0c-ok? (math-eval "x*exp(asinh(a*x))")))
  (for-each (lambda (s) (assert-true (c0c-ok? (math-eval s))))
            '("x*exp(atanh(a*x))" "exp(atanh(a*x))/x^2"))
  ; каскад integrate не оставляет интеграл невычисленным (именно этот тест уронил C0b)
  (let ((F (integrate (math-eval "x*exp(asinh(a*x))") 'x)))
    (assert-true (pair? F))
    (assert-true (not (equal? (car F) 'integrate)))))



; ---------- RUBI.CH-C0c: DeactivateTrig/ActivateTrig, ReduceInertTrig, UnifyInertTrigFunction ----------
; Источник: IUF.m:6180-6195 (ActivateTrig/DeactivateTrig), 6198-6219 (DeactivateTrigAux),
; 6492-6539 (ReduceInertTrig), 6542-7362 (UnifyInertTrigFunction).

(deftest "rubi-c: ReduceInertTrig — фаза m·π к 0 ≤ m < 1/2 (IUF.m:6509-6539)"
  ; 6522-6529: m≥1 — знак меняется у sin/cos/sec/csc, у tan/cot нет
  (assert-equal '(- (sin u)) (rubi::rubi-reduce-inert-trig 'sin 1 'u))
  (assert-equal '(tan u) (rubi::rubi-reduce-inert-trig 'tan 1 'u))
  ; 6530-6537: m≥1/2 — смена функции по симметрии
  (assert-equal '(cos u) (rubi::rubi-reduce-inert-trig 'sin 5/2 'u))
  (assert-equal '(- (cot u)) (rubi::rubi-reduce-inert-trig 'tan 1/2 'u))
  ; 6520-6521: m≥2 — вычитаем 2 (Mod[m,2]); 6511-6512: |m| мал — фаза остаётся
  (assert-equal '(- (sin u)) (rubi::rubi-reduce-inert-trig 'sin 3 'u))
  (assert-equal '(cos (+ (* 1/4 pi) u)) (rubi::rubi-reduce-inert-trig 'cos 1/4 'u)))

(deftest "rubi-c: DeactivateTrigAux сводит фазу только у линейного аргумента (IUF.m:6198-6219)"
  (assert-equal '(- (sin x)) (rubi::rubi-deactivate-trig-aux '(sin (+ x pi)) 'x))
  (assert-equal '(cos (* 2 x)) (rubi::rubi-deactivate-trig-aux '(cos (* 2 x)) 'x))
  ; нелинейный аргумент не трогаем (6201: TrigQ && LinearQ)
  (assert-equal '(sin (^ x 2)) (rubi::rubi-deactivate-trig-aux '(sin (^ x 2)) 'x)))

(deftest "rubi-c: UnifyInertTrigFunction — cos/cot/csc в sin/tan/sec (IUF.m:6549-7362)"
  (assert-equal '(sin (+ x (/ pi 2))) (rubi::rubi-unify-inert-trig-function '(cos x) 'x))
  (assert-equal '(^ (sin (+ x (/ pi 2))) 3) (rubi::rubi-unify-inert-trig-function '(^ (cos x) 3) 'x))
  (assert-equal '(^ (tan x) -1) (rubi::rubi-unify-inert-trig-function '(cot x) 'x))
  (assert-equal '(^ (sec x) -4) (rubi::rubi-unify-inert-trig-function '(^ (csc x) 4) 'x))
  ; sec и tan остаются; x-свободный множитель выносится (6549-6551)
  (assert-equal '(^ (sec x) 2) (rubi::rubi-unify-inert-trig-function '(^ (sec x) 2) 'x))
  (assert-equal '(* a (sin (+ x (/ pi 2)))) (rubi::rubi-unify-inert-trig-function '(* a (cos x)) 'x)))

(deftest "rubi-c: маскировка инертных голов вокруг simplify (DeactivateTrig/ActivateTrig)"
  (let ((m (rubi::rubi-inert-mask '(* (^ (tan x) 3) (sec x)) 'x)))
    (assert-true (not (contains-sym? (car m) 'tan)))
    (assert-true (not (contains-sym? (car m) 'sec)))
    (assert-equal '(* (^ (tan x) 3) (sec x)) (rubi::rubi-inert-unmask (car m) (cadr m))))
  ; нелинейный аргумент не маскируется (6201)
  (assert-true (pair? (car (rubi::rubi-inert-mask '(tan (^ x 2)) 'x))))
  ; маскировка выключена по умолчанию: правила порта ждут активированную форму (sec^2 -> cos^-2),
  ; с инертными головами теряются 4.5/4.6 (замер: 39/56 против 45/56 на наборе 4.2-4.6)
  (assert-true (not rubi::*rubi-inert-mask*))
  (assert-equal '(^ (sin (+ x (/ pi 2))) -2) (rubi::rubi-simplify-inert '(^ (sec x) 2) 'x)))

(deftest "rubi-c: rubi-inert-heads-of — набор голов для пропуска унификации (регрессия пилота C0c)"
  (assert-equal '(sin) (rubi::rubi-inert-heads-of '(* a (^ (sin x) 2))))
  (assert-equal '(sin cos) (rubi::rubi-inert-heads-of '(* (^ (sin x) 4) (^ (cos x) 3))))
  (assert-true (rubi::rubi-inert-multi-heads? '(* (sin x) (cos x))))
  (assert-true (not (rubi::rubi-inert-multi-heads? '(* a (sec x)))))
  (assert-true (not (rubi::rubi-inert-multi-heads? 'a))))

(deftest "rubi-c: rubi-simplify-inert — унификация только при одной голове (регрессия пилота C0c)"
  ; cos³ -> sin³ со сдвигом фазы: 4.2 идёт через правила 4.1 для sin^m
  (assert-equal '(^ (sin (+ x (/ pi 2))) 3) (rubi::rubi-simplify-inert '(^ (cos x) 3) 'x))
  ; одна голова + x-свободный множитель — унифицируется (6549-6551)
  (assert-equal '(* x (sin (+ x (/ pi 2)))) (rubi::rubi-simplify-inert '(* x (cos x)) 'x))
  ; произведение двух разных голов не унифицируется: клауз IUF.m:6566-7361 в порте нет, а частичная
  ; унификация переписывает один множитель и ломает правила 4.1 для sin^m*cos^n (пилот: -2 472 задачи 4.1)
  (assert-equal '(* (^ (cos x) 3) (^ (sin x) 4))
                (rubi::rubi-simplify-inert '(* (^ (sin x) 4) (^ (cos x) 3)) 'x))
  (assert-equal '(* (^ (cos x) 3) (^ (sin x) -4))
                (rubi::rubi-simplify-inert '(* (^ (cos x) 3) (^ (sin x) -4)) 'x))
  ; sec активируется simplify в cos^-1, произведение остаётся как есть (4.1: sin^m/cos)
  (assert-equal '(* (^ (cos x) -1) (^ (sin x) 4))
                (rubi::rubi-simplify-inert '(* (^ (sin x) 4) (sec x)) 'x))
  ; вложенные структуры (не моном по голове) не унифицируются: sqrt(a*cos(x)^2) остаётся в cos-форме
  ; (регрессия C0c.4: master 72 мс, с унификацией задача упиралась в бюджет)
  (assert-equal '(sqrt (* a (^ (cos x) 2))) (rubi::rubi-simplify-inert '(sqrt (* a (^ (cos x) 2))) 'x))
  ; а степени и суммы по одной голове унифицируются: формулы 4.2 для них находятся в sin-форме
  (assert-equal '(^ (sin (+ x (/ pi 2))) 1/2) (rubi::rubi-simplify-inert '(^ (cos x) 1/2) 'x))
  (assert-equal '(^ (* b (sin (+ x (/ pi 2)))) 3/2)
                (rubi::rubi-simplify-inert '(^ (* b (cos x)) 3/2) 'x))
  (assert-equal '(^ (+ 1 (sin (+ x (/ pi 2)))) -1) (rubi::rubi-simplify-inert '(^ (+ 1 (cos x)) -1) 'x)))
