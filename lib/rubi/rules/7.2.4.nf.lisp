(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.4 (f x)^m (d+e x^2)^p (a+b arccosh(c x))^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 7.2.4 #2" (* x (^ (+ ?a. (* ?b. (acosh (* ?c. x)))) ?n.) (^ (+ ?d (* ?e. (^ x 2))) -1)) (+ acosh) 3 (2 -1))
  ("Rubi 7.2.4 #5" (* (^ (+ ?a. (* ?b. (acosh (* ?c. x)))) ?n.) (^ x -1) (^ (+ ?d (* ?e. (^ x 2))) -1)) (+ acosh) 3 (2 -1 -1))
  ("Rubi 7.2.4 #8" (* (^ (+ ?d (* ?e. (^ x 2))) ?p.) (+ ?a. (* ?b. (acosh (* ?c. x)))) (^ x -1)) (acosh +) 3 (-1 2))
  ("Rubi 7.2.4 #34" (* (^ (* ?f. x) ?m) (^ (+ ?a. (* ?b. (acosh (* ?c. x)))) ?n.) (^ (+ ?d1 (* ?e1. x)) -1/2) (^ (+ ?d2 (* ?e2. x)) -1/2)) (+ + acosh) 4 (-1/2 -1/2))
  ("Rubi 7.2.4 #36" (* (^ x ?m) (^ (+ ?a. (* ?b. (acosh (* ?c. x)))) ?n.) (^ (+ ?d1 (* ?e1. x)) -1/2) (^ (+ ?d2 (* ?e2. x)) -1/2)) (+ + acosh) 4 (-1/2 -1/2))
  ("Rubi 7.2.4 #38" (* (^ (* ?f. x) ?m) (+ ?a. (* ?b. (acosh (* ?c. x)))) (^ (+ ?d1 (* ?e1. x)) -1/2) (^ (+ ?d2 (* ?e2. x)) -1/2)) (+ + acosh) 4 (-1/2 -1/2))
  ("Rubi 7.2.4 #40" (* (^ (* ?f. x) ?m.) (^ (+ ?a. (* ?b. (acosh (* ?c. x)))) ?n) (^ (+ ?d1 (* ?e1. x)) -1/2) (^ (+ ?d2 (* ?e2. x)) -1/2)) (+ + acosh) 4 (-1/2 -1/2))))
