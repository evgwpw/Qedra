(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.13 P(x) (e x)^m (c+d x)^n (a+b x^2)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 1.1.2.13 #2" (* ?Px (^ (+ ?c (* ?d. x)) ?n.) (^ (+ ?a (* ?b. (^ x 2))) ?p.) (^ x -1)) (+ +) 3 (-1 2))
  ("Rubi 1.1.2.13 #3" (* (^ (* ?e. x) ?m) ?Px (^ (+ ?c (* ?d. x)) -1/2) (^ (+ ?a (* ?b. (^ x 2))) -1/2)) (+ +) 3 (2 -1/2 -1/2))))
