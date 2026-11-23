(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.2 (d x)^m (a+b x^n+c x^(2 n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 1.2.3.2 #18" (* (^ (* ?d. x) ?m) (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) -1)) (+) 2 (-1))
  ("Rubi 1.2.3.2 #19" (* (^ x ?m) (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) -1)) (+) 2 (-1))
  ("Rubi 1.2.3.2 #20" (* (^ (* ?d. x) ?m) (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) -1)) (+) 2 (-1))
  ("Rubi 1.2.3.2 #21" (* (^ x ?m.) (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) -1)) (+) 2 (-1))
  ("Rubi 1.2.3.2 #22" (* (^ x ?m.) (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) -1)) (+) 2 (-1))
  ("Rubi 1.2.3.2 #23" (* (^ (* ?d. x) ?m) (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) -1)) (+) 2 (-1))
  ("Rubi 1.2.3.2 #24" (* (^ (* ?d. x) ?m.) (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) -1)) (+) 2 (-1))
  ("Rubi 1.2.3.2 #32" (* (^ (* ?d. x) ?m.) (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) -1)) (+) 2 (-1))))
