(module rubi)
; Rubi 4.17.3.0 — 8 Special functions/8.3 Exponential integral functions.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 8.3 #3" (* (ExpIntegralE 1 (* ?b. x)) (^ x -1)) (ExpIntegralE) 2 (-1))
  ("Rubi 8.3 #11" (* (ExpIntegralEi (* ?b. x)) (^ x -1)) (ExpIntegralEi) 2 (-1))
  ("Rubi 8.3 #12" (* (ExpIntegralEi (+ ?a. (* ?b. x))) (^ (+ ?c. (* ?d. x)) -1)) (ExpIntegralEi) 2 (-1))
  ("Rubi 8.3 #21" (* (ExpIntegralEi (* ?d. (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))))) (^ x -1)) (log ExpIntegralEi) 2 (-1))
  ("Rubi 8.3 #24" (* (LogIntegral (* ?b. x)) (^ x -1)) (LogIntegral) 2 (-1))
  ("Rubi 8.3 #25" (* (LogIntegral (+ ?a. (* ?b. x))) (^ (+ ?c. (* ?d. x)) -1)) (LogIntegral) 2 (-1))))
