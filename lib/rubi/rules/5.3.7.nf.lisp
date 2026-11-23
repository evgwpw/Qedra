(module rubi)
; Rubi 4.17.3.0 — 5 Inverse trig functions/5.3 Inverse tangent/5.3.7 Miscellaneous inverse tangent.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 5.3.7 #3" (* (atan (+ ?a. (* ?b. (^ x ?n)))) (^ x -1)) (atan) 2 (-1))
  ("Rubi 5.3.7 #4" (* (acot (+ ?a. (* ?b. (^ x ?n)))) (^ x -1)) (acot) 2 (-1))
  ("Rubi 5.3.7 #11" (* ?u. (^ (atan (* ?c. (^ (+ ?a. (* ?b. (^ x ?n.))) -1))) ?m.)) (atan) 1 (-1))
  ("Rubi 5.3.7 #12" (* ?u. (^ (acot (* ?c. (^ (+ ?a. (* ?b. (^ x ?n.))) -1))) ?m.)) (acot) 1 (-1))
  ("Rubi 5.3.7 #75" (* (atan ?v) (log ?w) (^ (+ ?a. (* ?b. x)) -1)) (log atan) 3 (-1))))
