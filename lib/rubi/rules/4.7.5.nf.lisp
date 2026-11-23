(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.7 Miscellaneous/4.7.5 Inert trig functions.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.7.5 #12" (* ?u (^ (cos (* ?c. (+ ?a. (* ?b. x)))) -2)) (cos) 1 (-2))
  ("Rubi 4.7.5 #14" (* ?u (^ (sin (* ?c. (+ ?a. (* ?b. x)))) -2)) (sin) 1 (-2))
  ("Rubi 4.7.5 #52" (* ?u (^ ?y -1)) () 1 (-1))
  ("Rubi 4.7.5 #53" (* ?u (^ ?y -1) (^ ?w -1)) () 2 (-1 -1))))
