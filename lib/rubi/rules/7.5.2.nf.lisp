(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.5 Inverse hyperbolic secant/7.5.2 Miscellaneous inverse hyperbolic secant.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 7.5.2 #15" (* ?u. (^ (asech (* ?c. (^ (+ ?a. (* ?b. (^ x ?n.))) -1))) ?m.)) (asech) 1 (-1))
  ("Rubi 7.5.2 #16" (* ?u. (^ (acsch (* ?c. (^ (+ ?a. (* ?b. (^ x ?n.))) -1))) ?m.)) (acsch) 1 (-1))
  ("Rubi 7.5.2 #22" (* (^ E (asech (* ?a. (^ x ?p.)))) (^ x -1)) (asech) 2 (-1))
  ("Rubi 7.5.2 #27" (* (^ E (asech (* ?c. x))) (^ (+ ?a (* ?b. (^ x 2))) -1)) (+ asech) 2 (2 -1))
  ("Rubi 7.5.2 #28" (* (^ E (acsch (* ?c. x))) (^ (+ ?a (* ?b. (^ x 2))) -1)) (+ acsch) 2 (2 -1))
  ("Rubi 7.5.2 #29" (* (^ (* ?d. x) ?m.) (^ E (asech (* ?c. x))) (^ (+ ?a (* ?b. (^ x 2))) -1)) (+ asech) 3 (2 -1))
  ("Rubi 7.5.2 #30" (* (^ (* ?d. x) ?m.) (^ E (acsch (* ?c. x))) (^ (+ ?a (* ?b. (^ x 2))) -1)) (+ acsch) 3 (2 -1))))
