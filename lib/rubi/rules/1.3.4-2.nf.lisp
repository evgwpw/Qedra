(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.3 Polynomial products/1.3.4 P(x) Q(x)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 1.3.4-2 #13" (* (+ ?A (* ?B. (^ x ?n))) (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x ?n)) (* ?d. (^ x ?n2))) -1)) (+ +) 2 (2 -1))
  ("Rubi 1.3.4-2 #14" (* (^ x ?m.) (+ ?A (* ?B. (^ x ?n.))) (^ (+ ?a (* ?b. (^ x ?k.)) (* ?c. (^ x ?n.)) (* ?d. (^ x ?n2))) -1)) (+ +) 3 (-1))
  ("Rubi 1.3.4-2 #15" (* (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) (^ (+ ?d (* ?e. (^ x 2)) (* ?f. (^ x 4)) (* ?g. (^ x 6))) -1)) (+ +) 2 (6 4 2 -1 4 2))
  ("Rubi 1.3.4-2 #16" (* (+ ?a (* ?c. (^ x 4))) (^ (+ ?d (* ?e. (^ x 2)) (* ?f. (^ x 4)) (* ?g. (^ x 6))) -1)) (+ +) 2 (6 4 2 -1 4))
  ("Rubi 1.3.4-2 #17" (* ?Pm (^ ?Qn -1)) () 1 (-1))
  ("Rubi 1.3.4-2 #19" (* ?Pm (^ ?Qn -1)) () 1 (-1))))
