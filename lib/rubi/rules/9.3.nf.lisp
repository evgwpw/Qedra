(module rubi)
; Rubi 4.17.3.0 — 9 Miscellaneous/9.3 Miscellaneous integration rules.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 9.3 #5" (* ?u (^ ?y -1)) () 1 (-1))
  ("Rubi 9.3 #6" (* ?u (^ ?y -1) (^ ?w -1)) () 2 (-1 -1))
  ("Rubi 9.3 #46" (* ?u (^ (+ ?a (* ?b. (^ x ?n))) -1)) (+) 1 (-1))
  ("Rubi 9.3 #49" (* ?u (^ (+ ?a. (* ?b. (^ x ?n.)) (* ?c. (^ x ?n2.))) -1)) (+) 1 (-1))
  ("Rubi 9.3 #52" (* ?u (^ x -1)) () 1 (-1))
  ("Rubi 9.3 #58" (^ (+ ?a (* ?b. (^ ?v 2))) -1) (+) 0 (2 -1))
  ("Rubi 9.3 #59" (^ (+ ?a (* ?b. (^ ?v ?n))) -1) (+) 0 (-1))
  ("Rubi 9.3 #60" (^ (+ ?a (* ?b. (^ ?v ?n))) -1) (+) 0 (-1))
  ("Rubi 9.3 #61" (* ?v (^ (+ ?a (* ?b. (^ ?u ?n.))) -1)) (+) 1 (-1))))
