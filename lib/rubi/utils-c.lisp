; rubi/utils-c.lisp — утилиты, нужные только правилам главы 4 (карточка C задания RUBI.CH, фаза 2).
; Файл грузит движок (lib/rubi/engine.lisp, rubi-chapter-utils) перед правилами главы 4.
; Источник: Rubi 4.17.3.0, commit 61e9c18ea248061cd83c67882f7c91a73cef912d, IntegrationUtilityFunctions.m.
; Здесь только то, чего в общем utils.lisp нет вовсе; общие утилиты (Known*IntegrandQ, InertTrigQ,
; TrigSimplifyQ) определены в utils.lisp и здесь не переопределяются.
(module rubi)

; Есть ли в выражении голова тригонометрии. В порте инертных голов нет (rubi-sin строит обычный sin),
; поэтому «инертная тригонометрия» и обычная — одно и то же.
(define (rubi-has-trig-head? u)
  (cond ((not (pair? u)) #f)
        ((member? (car u) (rubi-trig-heads)) #t)
        (else (any? rubi-has-trig-head? (cdr u)))))

; InertTrigFreeQ[u] — IUF.m:6173: u свободно от (инертных) тригонометрических функций.
(define (rubi-inert-trig-free-q u) (not (rubi-has-trig-head? u)))

; Алгебраическая функция от тригонометрии: только + - * / ^ и тригонометрия, у каждой — линейный аргумент
; (свободный от x аргумент — тоже линейный: e+0*x)
(define (rubi-trig-of-linear-q u x)
  (cond ((not (pair? u)) #t)
        ((member? (car u) (rubi-trig-heads))
         (or (rubi-freeq (cadr u) x) (rubi-linearq (cadr u) x)))
        ((member? (car u) (list '+ '- '* '/ '^))
         (every? (lambda (e) (rubi-trig-of-linear-q e x)) (cdr u)))
        (else #f)))

; FunctionOfTrigOfLinearQ[u,x] — IUF.m:4358: u — алгебраическая функция от тригонометрии
; линейной функции x (в исходнике — клауза (c+d*x)^m*(a+b*trig[e+f*x])^n или AlgebraicTrigFunctionQ).
(define (rubi-function-of-trig-of-linear-q u x)
  (and (rubi-has-trig-head? u) (rubi-trig-of-linear-q u x)))
