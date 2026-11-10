(module rubi)
; Rubi 4.17.3.0 — 6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.10 (c+d x)^m (a+b sinh)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.

  (rubi-add-rule "Rubi 6.1.10 #1" '(* (^ ?u ?m) (^ (+ ?a (* ?b (sinh ?v))) ?n)) '(and (and (rubi::rubi-freeq (list ?a ?b ?m ?n) (quote x)) (rubi::rubi-linearq (list ?u ?v) (quote x))) (not (rubi::rubi-linear-match-q (list ?u ?v) (quote x)))) '(rubi::rubi-int (* (^ (rubi::rubi-expand-to-sum u (quote x)) m) (^ (+ a (* b (sinh (rubi::rubi-expand-to-sum v (quote x))))) n)) (* (^ (rubi::rubi-expand-to-sum u (quote x)) m) (^ (+ a (* b (sinh (rubi::rubi-expand-to-sum v (quote x))))) n)) (quote x)))
  (rubi-add-rule "Rubi 6.1.10 #2" '(* (^ ?u ?m) (^ (+ ?a (* ?b (cosh ?v))) ?n)) '(and (and (rubi::rubi-freeq (list ?a ?b ?m ?n) (quote x)) (rubi::rubi-linearq (list ?u ?v) (quote x))) (not (rubi::rubi-linear-match-q (list ?u ?v) (quote x)))) '(rubi::rubi-int (* (^ (rubi::rubi-expand-to-sum u (quote x)) m) (^ (+ a (* b (cosh (rubi::rubi-expand-to-sum v (quote x))))) n)) (* (^ (rubi::rubi-expand-to-sum u (quote x)) m) (^ (+ a (* b (cosh (rubi::rubi-expand-to-sum v (quote x))))) n)) (quote x)))
