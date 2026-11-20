(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.5 Inverse hyperbolic secant/7.5.1 u (a+b arcsech(c x))^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 7.5.1 #5" (* (+ ?a. (* ?b. (asech (* ?c. x)))) (^ x -1)) (asech) 2 (-1))
  ("Rubi 7.5.1 #6" (* (+ ?a. (* ?b. (acsch (* ?c. x)))) (^ x -1)) (acsch) 2 (-1))
  ("Rubi 7.5.1 #11" (* (+ ?a. (* ?b. (asech (* ?c. x)))) (^ (+ ?d. (* ?e. x)) -1)) (asech) 2 (-1))
  ("Rubi 7.5.1 #13" (* (+ ?a. (* ?b. (acsch (* ?c. x)))) (^ (+ ?d. (* ?e. x)) -1)) (acsch) 2 (-1))))
