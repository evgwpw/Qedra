(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.5 Secant/4.5.2.1 (a+b sec)^m (c+d sec)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.5.2.1 #6" (* (^ (+ ?a (* ?b. (%csc (+ ?e. (* ?f. x))))) 3/2) (^ (+ ?c (* ?d. (%csc (+ ?e. (* ?f. x))))) ?n.)) (%csc + %csc +) 2 (3/2))
  ("Rubi 4.5.2.1 #7" (* (^ (+ ?a (* ?b. (%csc (+ ?e. (* ?f. x))))) 3/2) (^ (+ ?c (* ?d. (%csc (+ ?e. (* ?f. x))))) ?n.)) (%csc + %csc +) 2 (3/2))
  ("Rubi 4.5.2.1 #8" (* (^ (+ ?a (* ?b. (%csc (+ ?e. (* ?f. x))))) 5/2) (^ (+ ?c (* ?d. (%csc (+ ?e. (* ?f. x))))) ?n.)) (%csc + %csc +) 2 (5/2))
  ("Rubi 4.5.2.1 #17" (* (+ ?c (* ?d. (%csc (+ ?e. (* ?f. x))))) (^ (+ ?a (* ?b. (%csc (+ ?e. (* ?f. x))))) -1)) (%csc + %csc +) 2 (-1))
  ("Rubi 4.5.2.1 #25" (* (^ (+ ?a (* ?b. (%csc (+ ?e. (* ?f. x))))) 3/2) (^ (+ ?c (* ?d. (%csc (+ ?e. (* ?f. x))))) -1)) (%csc + %csc +) 2 (-1 3/2))
  ("Rubi 4.5.2.1 #26" (* (^ (+ ?a (* ?b. (%csc (+ ?e. (* ?f. x))))) 3/2) (^ (+ ?c (* ?d. (%csc (+ ?e. (* ?f. x))))) -1)) (%csc + %csc +) 2 (-1 3/2))
  ("Rubi 4.5.2.1 #37" (* (^ (+ ?a (* ?b. (%csc (+ ?e. (* ?f. x))))) 1/2) (^ (+ ?c (* ?d. (%csc (+ ?e. (* ?f. x))))) -3/2)) (%csc + %csc +) 2 (-3/2 1/2))
  ("Rubi 4.5.2.1 #44" (* (^ (+ ?a. (* ?b. (%sec (+ ?e. (* ?f. x))))) ?m.) (^ (* ?d. (^ (%sec (+ ?e. (* ?f. x))) -1)) ?n)) (%sec %sec) 2 (-1))
  ("Rubi 4.5.2.1 #45" (* (^ (+ ?a. (* ?b. (%csc (+ ?e. (* ?f. x))))) ?m.) (^ (* ?d. (^ (%csc (+ ?e. (* ?f. x))) -1)) ?n)) (%csc %csc) 2 (-1))))
