(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.9 P(x) (a+b x+c x^2)^p (d+e x+f x^2)^q.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 1.2.1.9 #16" (* ?Px (^ (+ ?a (* ?b. x) (* ?c. (^ x 2))) -1) (^ (+ ?d (* ?e. x) (* ?f. (^ x 2))) -1)) (+ +) 2 (2 -1 2 -1))
  ("Rubi 1.2.1.9 #17" (* ?Px (^ (+ ?a (* ?b. x) (* ?c. (^ x 2))) -1) (^ (+ ?d (* ?f. (^ x 2))) -1)) (+ +) 2 (2 -1 2 -1))
  ("Rubi 1.2.1.9 #18" (* ?Px (^ (+ ?a (* ?b. x) (* ?c. (^ x 2))) -1) (^ (+ ?d. (* ?e. x) (* ?f. (^ x 2))) -1/2)) (+ +) 2 (2 -1/2 2 -1))
  ("Rubi 1.2.1.9 #19" (* ?Px (^ (+ ?a (* ?c. (^ x 2))) -1) (^ (+ ?d. (* ?e. x) (* ?f. (^ x 2))) -1/2)) (+ +) 2 (2 -1/2 2 -1))
  ("Rubi 1.2.1.9 #20" (* ?Px (^ (+ ?a (* ?b. x) (* ?c. (^ x 2))) -1) (^ (+ ?d. (* ?f. (^ x 2))) -1/2)) (+) 2 (2 -1/2 2 -1))))
