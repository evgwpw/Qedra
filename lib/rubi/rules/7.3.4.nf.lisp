(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.4 Miscellaneous inverse hyperbolic tangent.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 7.3.4 #3" (* (atanh (+ ?a. (* ?b. (^ x ?n.)))) (^ x -1)) (atanh) 2 (-1))
  ("Rubi 7.3.4 #4" (* (acoth (+ ?a. (* ?b. (^ x ?n.)))) (^ x -1)) (acoth) 2 (-1))
  ("Rubi 7.3.4 #11" (* ?u. (^ (atanh (* ?c. (^ (+ ?a. (* ?b. (^ x ?n.))) -1))) ?m.)) (atanh) 1 (-1))
  ("Rubi 7.3.4 #12" (* ?u. (^ (acoth (* ?c. (^ (+ ?a. (* ?b. (^ x ?n.))) -1))) ?m.)) (acoth) 1 (-1))))
