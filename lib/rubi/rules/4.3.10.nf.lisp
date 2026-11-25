(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.10 (c+d x)^m (a+b tan)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.3.10 #8" (* (^ (+ ?c. (* ?d. x)) ?m.) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan +) 2 (-1))
  ("Rubi 4.3.10 #9" (* (^ (+ ?c. (* ?d. x)) -2) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan +) 2 (-1 -2))
  ("Rubi 4.3.10 #10" (* (^ (+ ?c. (* ?d. x)) ?m) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan +) 2 (-1))
  ("Rubi 4.3.10 #11" (* (^ (+ ?c. (* ?d. x)) -1) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan +) 2 (-1 -1))
  ("Rubi 4.3.10 #12" (* (^ (+ ?c. (* ?d. x)) ?m) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan +) 2 (-1))
  ("Rubi 4.3.10 #16" (* (^ (+ ?c. (* ?d. x)) ?m.) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?k. pi) (* ?f. x))))) -1)) (+ tan +) 2 (-1))
  ("Rubi 4.3.10 #17" (* (^ (+ ?c. (* ?d. x)) ?m.) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan +) 2 (-1))
  ("Rubi 4.3.10 #18" (* (+ ?c. (* ?d. x)) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -2)) (tan +) 2 (-2))))
