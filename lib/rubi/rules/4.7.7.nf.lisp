(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.7 Miscellaneous/4.7.7 F^(c (a+b x)) trig(d+e x)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.7.7 #34" (* (^ ?F (* ?c. (+ ?a. (* ?b. x)))) (+ ?h (* ?i. (cos (+ ?d. (* ?e. x))))) (^ (+ ?f (* ?g. (sin (+ ?d. (* ?e. x))))) -1)) (sin + cos +) 3 (-1))
  ("Rubi 4.7.7 #35" (* (^ ?F (* ?c. (+ ?a. (* ?b. x)))) (+ ?h (* ?i. (sin (+ ?d. (* ?e. x))))) (^ (+ ?f (* ?g. (cos (+ ?d. (* ?e. x))))) -1)) (cos + sin +) 3 (-1))))
