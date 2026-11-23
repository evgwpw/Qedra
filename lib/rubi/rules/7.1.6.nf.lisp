(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.6 Miscellaneous inverse hyperbolic sine.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 7.1.6 #7" (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. (^ x 2)))))) -1) (+ asinh) 0 (2 -1))
  ("Rubi 7.1.6 #9" (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. (^ x 2)))))) -3/2) (+ asinh) 0 (2 -3/2))
  ("Rubi 7.1.6 #10" (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. (^ x 2)))))) -2) (+ asinh) 0 (2 -2))
  ("Rubi 7.1.6 #12" (* (^ (asinh (* ?a. (^ x ?p))) ?n.) (^ x -1)) (asinh) 2 (-1))
  ("Rubi 7.1.6 #13" (* ?u. (^ (asinh (* ?c. (^ (+ ?a. (* ?b. (^ x ?n.))) -1))) ?m.)) (asinh) 1 (-1))))
