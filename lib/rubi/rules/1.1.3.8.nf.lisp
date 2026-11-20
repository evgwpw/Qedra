(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.1 Binomial products/1.1.3 General/1.1.3.8 P(x) (c x)^m (a+b x^n)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 1.1.3.8 #1" (* (^ x ?m.) (+ ?e (* ?f. (^ x ?q.)) (* ?g. (^ x ?r.)) (* ?h. (^ x ?n.))) (^ (+ ?a (* ?c. (^ x ?n.))) -3/2)) (+ +) 3 (-3/2))
  ("Rubi 1.1.3.8 #2" (* (^ (* ?d x) ?m.) (+ ?e (* ?f. (^ x ?q.)) (* ?g. (^ x ?r.)) (* ?h. (^ x ?n.))) (^ (+ ?a (* ?c. (^ x ?n.))) -3/2)) (+ +) 3 (-3/2))
  ("Rubi 1.1.3.8 #12" (* (^ x 2) ?P4 (^ (+ ?a (* ?b. (^ x 4))) -3/2)) (+) 2 (4 -3/2 2))
  ("Rubi 1.1.3.8 #16" (* (^ (* ?c. x) ?m.) ?Pq (^ (+ ?a (* ?b. (^ x ?n))) -1)) (+) 2 (-1))
  ("Rubi 1.1.3.8 #17" (* ?Pq (^ x -1) (^ (+ ?a (* ?b. (^ x ?n))) -1/2)) (+) 2 (-1/2 -1))
  ("Rubi 1.1.3.8 #19" (* (^ (* ?c. x) ?m.) ?Pq (^ (+ ?a (* ?b. (^ x ?n))) -1)) (+) 2 (-1))))
