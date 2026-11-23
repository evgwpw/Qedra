(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.8 P(x) (d+e x)^q (a+b x^2+c x^4)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 1.2.2.8 #5" (* (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) ?p.) (^ (+ ?d (* ?e. x)) -1)) (+ +) 2 (-1 4 2))
  ("Rubi 1.2.2.8 #6" (* (^ (+ ?a (* ?c. (^ x 4))) ?p.) (^ (+ ?d (* ?e. x)) -1)) (+ +) 2 (-1 4))
  ("Rubi 1.2.2.8 #17" (* (+ ?A (* ?B. x)) (^ (+ ?d (* ?e. x)) -1) (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) -1/2)) (+ + +) 3 (4 2 -1/2 -1))
  ("Rubi 1.2.2.8 #18" (* ?Px (^ (+ ?d (* ?e. x)) -1) (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) -1/2)) (+ +) 2 (4 2 -1/2 -1))
  ("Rubi 1.2.2.8 #19" (* ?Px (^ (+ ?d (* ?e. x)) -1) (^ (+ ?a (* ?c. (^ x 4))) -1/2)) (+ +) 2 (4 -1/2 -1))
  ("Rubi 1.2.2.8 #20" (* ?Px (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) ?p.) (^ (+ ?d (* ?e. x)) -1)) (+ +) 2 (-1 4 2))
  ("Rubi 1.2.2.8 #21" (* ?Px (^ (+ ?a (* ?c. (^ x 4))) ?p.) (^ (+ ?d (* ?e. x)) -1)) (+ +) 2 (-1 4))))
