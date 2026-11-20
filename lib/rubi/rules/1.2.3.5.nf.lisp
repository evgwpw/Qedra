(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.5 P(x) (a+b x^n+c x^(2 n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 1.2.3.5 #12" (* ?Pq (^ (+ ?a (* ?b. (^ x ?n.)) (* ?c. (^ x ?n2))) -1)) (+) 1 (-1))
  ("Rubi 1.2.3.5 #18" (* ?Pq (^ (+ ?a (* ?b. (^ x ?n.)) (* ?c. (^ x ?n2.))) -1)) (+) 1 (-1))
  ("Rubi 1.2.3.5 #20" (* ?Pq (^ (+ ?a (* ?b. (^ x ?n.)) (* ?c. (^ x ?n2.))) -1)) (+) 1 (-1))))
