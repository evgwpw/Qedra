(module rubi)
; Rubi 4.17.3.0 — 8 Special functions/8.5 Hyperbolic integral functions.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 8.5 #3" (* (SinhIntegral (* ?b. x)) (^ x -1)) (SinhIntegral) 2 (-1))
  ("Rubi 8.5 #4" (* (CoshIntegral (* ?b. x)) (^ x -1)) (CoshIntegral) 2 (-1))
  ("Rubi 8.5 #27" (* (?F (* ?d. (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))))) (^ x -1)) (log) 2 (-1))))
