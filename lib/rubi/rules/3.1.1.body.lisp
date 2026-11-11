(module rubi)
; Rubi 4.17.3.0 — 3 Logarithms/3.1.1 (a+b log(c x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Тела правил: ("id" условие правая-часть); читаются лениво (rubi-load-bodies).
(rubi-bodies-data '(
  ("Rubi 3.1.1 #1" (rubi::rubi-freeq (list ?c ?n) (quote x)) (- (* (quote x) (log (* c (^ (quote x) n)))) (* n (quote x))))
  ("Rubi 3.1.1 #2" (and (and (rubi::rubi-freeq (list ?a ?b ?c ?n) (quote x)) (rubi::rubi-gtq ?p 0)) (rubi::rubi-integerq (* 2 ?p))) (- (* (quote x) (^ (+ a (* b (log (* c (^ (quote x) n))))) p)) (* b n p (rubi::rubi-int (^ (+ a (* b (log (* c (^ (quote x) n))))) (- p 1)) (^ (+ a (* b (log (* c (^ (quote x) n))))) (- p 1)) (quote x)))))
  ("Rubi 3.1.1 #3" (and (and (rubi::rubi-freeq (list ?a ?b ?c ?n) (quote x)) (rubi::rubi-ltq ?p (- 1))) (rubi::rubi-integerq (* 2 ?p))) (- (/ (* (quote x) (^ (+ a (* b (log (* c (^ (quote x) n))))) (+ p 1))) (* b n (+ p 1))) (* (/ 1 (* b n (+ p 1))) (rubi::rubi-int (^ (+ a (* b (log (* c (^ (quote x) n))))) (+ p 1)) (^ (+ a (* b (log (* c (^ (quote x) n))))) (+ p 1)) (quote x)))))
  ("Rubi 3.1.1 #4" (rubi::rubi-freeq ?c (quote x)) (/ (rubi::rubi-log-integral (* c (quote x))) c))
  ("Rubi 3.1.1 #5" (and (rubi::rubi-freeq (list ?a ?b ?c ?p) (quote x)) (rubi::rubi-integerq (/ 1 ?n))) (* (/ 1 (* n (^ c (/ 1 n)))) (rubi::rubi-subst-pat (rubi::rubi-int (* (^ (exp 1) (/ (quote x) n)) (^ (+ a (* b (quote x))) p)) (* (^ (exp 1) (/ (quote x) n)) (^ (+ a (* b (quote x))) p)) (quote x)) (quote x) (log (* c (^ (quote x) n))))))
  ("Rubi 3.1.1 #6" (rubi::rubi-freeq (list ?a ?b ?c ?n ?p) (quote x)) (* (/ (quote x) (* n (^ (* c (^ (quote x) n)) (/ 1 n)))) (rubi::rubi-subst-pat (rubi::rubi-int (* (^ (exp 1) (/ (quote x) n)) (^ (+ a (* b (quote x))) p)) (* (^ (exp 1) (/ (quote x) n)) (^ (+ a (* b (quote x))) p)) (quote x)) (quote x) (log (* c (^ (quote x) n))))))))
