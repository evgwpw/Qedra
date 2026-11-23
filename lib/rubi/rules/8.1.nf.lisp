(module rubi)
; Rubi 4.17.3.0 — 8 Special functions/8.1 Error functions.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 8.1 #10" (* (erf (* ?b. x)) (^ x -1)) (erf) 2 (-1))
  ("Rubi 8.1 #11" (* (Erfc (* ?b. x)) (^ x -1)) (Erfc) 2 (-1))
  ("Rubi 8.1 #12" (* (Erfi (* ?b. x)) (^ x -1)) (Erfi) 2 (-1))
  ("Rubi 8.1 #40" (* (^ E (+ ?c. (* ?d. (^ x 2)))) (erf (* ?b. x)) (^ x -1)) (erf) 3 (-1 2))
  ("Rubi 8.1 #41" (* (^ E (+ ?c. (* ?d. (^ x 2)))) (Erfc (* ?b. x)) (^ x -1)) (Erfc) 3 (-1 2))
  ("Rubi 8.1 #42" (* (^ E (+ ?c. (* ?d. (^ x 2)))) (Erfi (* ?b. x)) (^ x -1)) (Erfi) 3 (-1 2))
  ("Rubi 8.1 #52" (* (?F (* ?d. (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))))) (^ x -1)) (log) 2 (-1))))
