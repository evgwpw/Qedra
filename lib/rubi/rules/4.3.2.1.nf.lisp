(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.2.1 (a+b tan)^m (c+d tan)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.3.2.1 #9" (* (+ ?c (* ?d. (tan (+ ?e. (* ?f. x))))) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan + tan +) 2 (-1))
  ("Rubi 4.3.2.1 #10" (* (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) (^ (+ ?a. (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan) 2 (-1))
  ("Rubi 4.3.2.1 #20" (* (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) 2) (^ (+ ?a. (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan) 2 (-1 2))
  ("Rubi 4.3.2.1 #28" (* (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) ?n) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan + tan) 2 (-1))
  ("Rubi 4.3.2.1 #29" (* (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) ?n) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan + tan) 2 (-1))
  ("Rubi 4.3.2.1 #30" (* (^ (+ ?a. (* ?b. (tan (+ ?e. (* ?f. x))))) -1) (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan) 2 (-1 -1))
  ("Rubi 4.3.2.1 #31" (* (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) ?n) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan + tan) 2 (-1))
  ("Rubi 4.3.2.1 #33" (* (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) 3/2) (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan +) 2 (-1 3/2))
  ("Rubi 4.3.2.1 #34" (* (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) 3/2) (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) -1/2)) (tan tan +) 2 (-1/2 3/2))
  ("Rubi 4.3.2.1 #41" (* (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) ?m) (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan +) 2 (-1))
  ("Rubi 4.3.2.1 #50" (* (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1) (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan +) 2 (-1 -1))
  ("Rubi 4.3.2.1 #52" (* (^ (+ ?a. (* ?b. (tan (+ ?e. (* ?f. x))))) 3/2) (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan) 2 (-1 3/2))
  ("Rubi 4.3.2.1 #53" (* (^ (+ ?a. (* ?b. (tan (+ ?e. (* ?f. x))))) ?m) (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan) 2 (-1))
  ("Rubi 4.3.2.1 #55" (* (^ (+ ?a. (* ?b. (tan (+ ?e. (* ?f. x))))) ?m.) (^ (* ?d. (^ (tan (+ ?e. (* ?f. x))) -1)) ?n)) (tan tan) 2 (-1))
  ("Rubi 4.3.2.1 #56" (* (^ (+ ?a. (* ?b. (cot (+ ?e. (* ?f. x))))) ?m.) (^ (* ?d. (^ (cot (+ ?e. (* ?f. x))) -1)) ?n)) (cot cot) 2 (-1))))
