(module rubi)
; Rubi 4.17.3.0 — 8 Special functions/8.6 Gamma functions.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 8.6 #2" (* (gamma 0 (* ?b. x)) (^ x -1)) (gamma) 2 (-1))
  ("Rubi 8.6 #3" (* (gamma ?n (* ?b. x)) (^ x -1)) (gamma) 2 (-1))
  ("Rubi 8.6 #4" (* (gamma ?n (* ?b. x)) (^ x -1)) (gamma) 2 (-1))
  ("Rubi 8.6 #5" (* (gamma ?n (* ?b. x)) (^ x -1)) (gamma) 2 (-1))
  ("Rubi 8.6 #8" (* (gamma ?n (+ ?a. (* ?b. x))) (^ (+ ?c. (* ?d. x)) -1)) (gamma) 2 (-1))
  ("Rubi 8.6 #21" (* (gamma ?p (* ?d. (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))))) (^ x -1)) (log gamma) 2 (-1))))
