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
