(module rubi)
; Rubi 4.17.3.0 — 5 Inverse trig functions/5.1 Inverse sine/5.1.6 Miscellaneous inverse sine.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 5.1.6 #14" (^ (+ ?a. (* ?b. (asin (+ ?c (* ?d. (^ x 2)))))) -1) (+ asin) 0 (2 -1))
  ("Rubi 5.1.6 #15" (^ (+ ?a. (* ?b. (acos (+ 1 (* ?d. (^ x 2)))))) -1) (+ acos) 0 (2 -1))
  ("Rubi 5.1.6 #16" (^ (+ ?a. (* ?b. (acos (+ -1 (* ?d. (^ x 2)))))) -1) (+ acos) 0 (2 -1))
  ("Rubi 5.1.6 #20" (^ (+ ?a. (* ?b. (asin (+ ?c (* ?d. (^ x 2)))))) -3/2) (+ asin) 0 (2 -3/2))
  ("Rubi 5.1.6 #21" (^ (+ ?a. (* ?b. (acos (+ 1 (* ?d. (^ x 2)))))) -3/2) (+ acos) 0 (2 -3/2))
  ("Rubi 5.1.6 #22" (^ (+ ?a. (* ?b. (acos (+ -1 (* ?d. (^ x 2)))))) -3/2) (+ acos) 0 (2 -3/2))
  ("Rubi 5.1.6 #23" (^ (+ ?a. (* ?b. (asin (+ ?c (* ?d. (^ x 2)))))) -2) (+ asin) 0 (2 -2))
  ("Rubi 5.1.6 #24" (^ (+ ?a. (* ?b. (acos (+ 1 (* ?d. (^ x 2)))))) -2) (+ acos) 0 (2 -2))
  ("Rubi 5.1.6 #25" (^ (+ ?a. (* ?b. (acos (+ -1 (* ?d. (^ x 2)))))) -2) (+ acos) 0 (2 -2))
  ("Rubi 5.1.6 #28" (* (^ (asin (* ?a. (^ x ?p))) ?n.) (^ x -1)) (asin) 2 (-1))
  ("Rubi 5.1.6 #29" (* (^ (acos (* ?a. (^ x ?p))) ?n.) (^ x -1)) (acos) 2 (-1))
  ("Rubi 5.1.6 #30" (* ?u. (^ (asin (* ?c. (^ (+ ?a. (* ?b. (^ x ?n.))) -1))) ?m.)) (asin) 1 (-1))
  ("Rubi 5.1.6 #31" (* ?u. (^ (acos (* ?c. (^ (+ ?a. (* ?b. (^ x ?n.))) -1))) ?m.)) (acos) 1 (-1))))
