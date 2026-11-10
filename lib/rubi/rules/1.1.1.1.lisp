(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.1 (a+b x)^m.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.

  (rubi-add-rule "Rubi 1.1.1.1 #1" '(/ 1 x) '() '(log (quote x)))
  (rubi-add-rule "Rubi 1.1.1.1 #2" '(^ x ?m) '(and (rubi::rubi-freeq ?m (quote x)) (rubi::rubi-neq ?m (- 1))) '(/ (^ (quote x) (+ m 1)) (+ m 1)))
  (rubi-add-rule "Rubi 1.1.1.1 #3" '(/ 1 (+ ?a (* ?b x))) '(rubi::rubi-freeq (list ?a ?b) (quote x)) '(/ (log (rubi::rubi-remove-content (+ a (* b (quote x))) (quote x))) b))
  (rubi-add-rule "Rubi 1.1.1.1 #4" '(^ (+ ?a (* ?b x)) ?m) '(and (rubi::rubi-freeq (list ?a ?b ?m) (quote x)) (rubi::rubi-neq ?m (- 1))) '(/ (^ (+ a (* b (quote x))) (+ m 1)) (* b (+ m 1))))
  (rubi-add-rule "Rubi 1.1.1.1 #5" '(^ (+ ?a (* ?b ?u)) ?m) '(and (and (rubi::rubi-freeq (list ?a ?b ?m) (quote x)) (rubi::rubi-linearq ?u (quote x))) (rubi::rubi-neq ?u (quote x))) '(* (/ 1 (rubi::rubi-coefficient u (quote x) 1)) (subst (list (list (quote x) u)) (rubi::rubi-int (^ (+ a (* b (quote x))) m) (^ (+ a (* b (quote x))) m) (quote x)))))
