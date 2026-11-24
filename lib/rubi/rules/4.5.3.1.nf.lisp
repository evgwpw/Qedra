(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.5 Secant/4.5.3.1 (a+b sec)^m (d sec)^n (A+B sec).m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.5.3.1 #3" (* (%csc (+ ?e. (* ?f. x))) (+ ?A (* ?B. (%csc (+ ?e. (* ?f. x))))) (^ (+ ?a (* ?b. (%csc (+ ?e. (* ?f. x))))) -1)) (%csc + %csc + %csc) 3 (-1))
  ("Rubi 4.5.3.1 #40" (* (+ ?A (* ?B. (%csc (+ ?e. (* ?f. x))))) (^ (* ?d. (%csc (+ ?e. (* ?f. x)))) -1/2) (^ (+ ?a (* ?b. (%csc (+ ?e. (* ?f. x))))) -1/2)) (%csc + %csc %csc +) 3 (-1/2 -1/2))
  ("Rubi 4.5.3.1 #43" (* (^ (* ?d. (%csc (+ ?e. (* ?f. x)))) ?n) (+ ?A (* ?B. (%csc (+ ?e. (* ?f. x))))) (^ (+ ?a (* ?b. (%csc (+ ?e. (* ?f. x))))) -1)) (%csc + %csc + %csc) 3 (-1))))
