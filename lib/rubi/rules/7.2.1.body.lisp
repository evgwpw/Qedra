(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.1 (a+b arccosh(c x))^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Тела правил: ("id" условие правая-часть); читаются лениво (rubi-load-bodies).
(rubi-bodies-data '(
  ("Rubi 7.2.1 #1" (and (rubi::rubi-freeq (list ?a ?b ?c) (quote x)) (rubi::rubi-gtq ?n 0)) (- (* (quote x) (^ (+ a (* b (acosh (* c (quote x))))) n)) (* b c n (rubi::rubi-int (/ (* (quote x) (^ (+ a (* b (acosh (* c (quote x))))) (- n 1))) (* (sqrt (+ 1 (* c (quote x)))) (sqrt (+ (- 1) (* c (quote x)))))) (/ (* (quote x) (^ (+ a (* b (acosh (* c (quote x))))) (- n 1))) (* (sqrt (+ 1 (* c (quote x)))) (sqrt (+ (- 1) (* c (quote x)))))) (quote x)))))
  ("Rubi 7.2.1 #2" (and (rubi::rubi-freeq (list ?a ?b ?c) (quote x)) (rubi::rubi-ltq ?n (- 1))) (- (/ (* (sqrt (+ 1 (* c (quote x)))) (sqrt (+ (- 1) (* c (quote x)))) (^ (+ a (* b (acosh (* c (quote x))))) (+ n 1))) (* b c (+ n 1))) (* (/ c (* b (+ n 1))) (rubi::rubi-int (/ (* (quote x) (^ (+ a (* b (acosh (* c (quote x))))) (+ n 1))) (* (sqrt (+ 1 (* c (quote x)))) (sqrt (+ (- 1) (* c (quote x)))))) (/ (* (quote x) (^ (+ a (* b (acosh (* c (quote x))))) (+ n 1))) (* (sqrt (+ 1 (* c (quote x)))) (sqrt (+ (- 1) (* c (quote x)))))) (quote x)))))
  ("Rubi 7.2.1 #3" (rubi::rubi-freeq (list ?a ?b ?c ?n) (quote x)) (* (/ 1 (* b c)) (rubi::rubi-subst-pat (rubi::rubi-int (* (^ (quote x) n) (sinh (+ (/ (- a) b) (/ (quote x) b)))) (* (^ (quote x) n) (sinh (+ (/ (- a) b) (/ (quote x) b)))) (quote x)) (quote x) (+ a (* b (acosh (* c (quote x))))))))))
