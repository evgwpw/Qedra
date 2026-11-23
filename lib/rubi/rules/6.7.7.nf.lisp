(module rubi)
; Rubi 4.17.3.0 — 6 Hyperbolic functions/6.7 Miscellaneous/6.7.7 F^(c (a+b x)) hyper(d+e x)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 6.7.7 #32" (* (^ ?F (* ?c. (+ ?a. (* ?b. x)))) (+ ?h (* ?i. (cosh (+ ?d. (* ?e. x))))) (^ (+ ?f (* ?g. (sinh (+ ?d. (* ?e. x))))) -1)) (sinh + cosh +) 3 (-1))
  ("Rubi 6.7.7 #33" (* (^ ?F (* ?c. (+ ?a. (* ?b. x)))) (+ ?h (* ?i. (sinh (+ ?d. (* ?e. x))))) (^ (+ ?f (* ?g. (cosh (+ ?d. (* ?e. x))))) -1)) (cosh + sinh +) 3 (-1))))
