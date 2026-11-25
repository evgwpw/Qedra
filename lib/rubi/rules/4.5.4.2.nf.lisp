(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.5 Secant/4.5.4.2 (a+b sec)^m (d sec)^n (A+B sec+C sec^2).m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.5.4.2 #35" (* (+ ?A. (* ?B. (csc (+ ?e. (* ?f. x)))) (* ?C. (^ (csc (+ ?e. (* ?f. x))) 2))) (^ (* ?d. (csc (+ ?e. (* ?f. x)))) -1/2) (^ (+ ?a (* ?b. (csc (+ ?e. (* ?f. x))))) -1)) (csc + csc csc csc +) 3 (-1 -1/2 2))
  ("Rubi 4.5.4.2 #36" (* (+ ?A. (* ?C. (^ (csc (+ ?e. (* ?f. x))) 2))) (^ (* ?d. (csc (+ ?e. (* ?f. x)))) -1/2) (^ (+ ?a (* ?b. (csc (+ ?e. (* ?f. x))))) -1)) (csc + csc csc) 3 (-1 -1/2 2))
  ("Rubi 4.5.4.2 #37" (* (+ ?A. (* ?B. (csc (+ ?e. (* ?f. x)))) (* ?C. (^ (csc (+ ?e. (* ?f. x))) 2))) (^ (* ?d. (csc (+ ?e. (* ?f. x)))) -1/2) (^ (+ ?a (* ?b. (csc (+ ?e. (* ?f. x))))) -1/2)) (csc + csc csc csc +) 3 (-1/2 -1/2 2))
  ("Rubi 4.5.4.2 #38" (* (+ ?A. (* ?C. (^ (csc (+ ?e. (* ?f. x))) 2))) (^ (* ?d. (csc (+ ?e. (* ?f. x)))) -1/2) (^ (+ ?a (* ?b. (csc (+ ?e. (* ?f. x))))) -1/2)) (csc + csc csc) 3 (-1/2 -1/2 2))))
