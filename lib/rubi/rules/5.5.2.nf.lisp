(module rubi)
; Rubi 4.17.3.0 — 5 Inverse trig functions/5.5 Inverse secant/5.5.2 Miscellaneous inverse secant.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 5.5.2 #15" (* ?u. (^ (asec (* ?c. (^ (+ ?a. (* ?b. (^ x ?n.))) -1))) ?m.)) (asec) 1 (-1))
  ("Rubi 5.5.2 #16" (* ?u. (^ (acsc (* ?c. (^ (+ ?a. (* ?b. (^ x ?n.))) -1))) ?m.)) (acsc) 1 (-1))))
