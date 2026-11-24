(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.5 Secant/4.5.1.1 (a+b sec)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.5.1.1 #15" (^ (+ ?a (* ?b. (%csc (+ ?c. (* ?d. x))))) 3/2) (%csc +) 0 (3/2))
  ("Rubi 4.5.1.1 #17" (^ (+ ?a (* ?b. (%csc (+ ?c. (* ?d. x))))) -1) (%csc +) 0 (-1))))
