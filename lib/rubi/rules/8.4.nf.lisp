(module rubi)
; Rubi 4.17.3.0 — 8 Special functions/8.4 Trig integral functions.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 8.4 #3" (* (SinIntegral (* ?b. x)) (^ x -1)) (SinIntegral) 2 (-1))
  ("Rubi 8.4 #4" (* (CosIntegral (* ?b. x)) (^ x -1)) (CosIntegral) 2 (-1))
  ("Rubi 8.4 #27" (* (?F (* ?d. (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))))) (^ x -1)) (log) 2 (-1))))
