(module rubi)
; Rubi 4.17.3.0 — 6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.10 (c+d x)^m (a+b sinh)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Тела правил: ("id" условие правая-часть); читаются лениво (rubi-load-bodies).
(rubi-bodies-data '(
  ("Rubi 6.1.10 #1" (and (and (rubi::rubi-freeq (list ?a ?b ?m ?n) (quote x)) (rubi::rubi-linearq (list ?u ?v) (quote x))) (not (rubi::rubi-linear-match-q (list ?u ?v) (quote x)))) (rubi::rubi-int (* (^ (rubi::rubi-expand-to-sum u (quote x)) m) (^ (+ a (* b (sinh (rubi::rubi-expand-to-sum v (quote x))))) n)) (* (^ (rubi::rubi-expand-to-sum u (quote x)) m) (^ (+ a (* b (sinh (rubi::rubi-expand-to-sum v (quote x))))) n)) (quote x)))
  ("Rubi 6.1.10 #2" (and (and (rubi::rubi-freeq (list ?a ?b ?m ?n) (quote x)) (rubi::rubi-linearq (list ?u ?v) (quote x))) (not (rubi::rubi-linear-match-q (list ?u ?v) (quote x)))) (rubi::rubi-int (* (^ (rubi::rubi-expand-to-sum u (quote x)) m) (^ (+ a (* b (cosh (rubi::rubi-expand-to-sum v (quote x))))) n)) (* (^ (rubi::rubi-expand-to-sum u (quote x)) m) (^ (+ a (* b (cosh (rubi::rubi-expand-to-sum v (quote x))))) n)) (quote x)))))
