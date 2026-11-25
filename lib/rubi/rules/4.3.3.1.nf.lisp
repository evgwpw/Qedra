(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.3.1 (a+b tan)^m (c+d tan)^n (A+B tan).m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.3.3.1 #2" (* (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) (+ ?A. (* ?B. (tan (+ ?e. (* ?f. x))))) (^ (+ ?a. (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan tan) 3 (-1))
  ("Rubi 4.3.3.1 #13" (* (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) ?m) (+ ?A. (* ?B. (tan (+ ?e. (* ?f. x))))) (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan tan +) 3 (-1))
  ("Rubi 4.3.3.1 #19" (* (^ (+ ?a. (* ?b. (tan (+ ?e. (* ?f. x))))) 2) (+ ?A. (* ?B. (tan (+ ?e. (* ?f. x))))) (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan tan) 3 (-1 2))
  ("Rubi 4.3.3.1 #24" (* (+ ?A. (* ?B. (tan (+ ?e. (* ?f. x))))) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) -1) (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan + tan) 3 (-1 -1))
  ("Rubi 4.3.3.1 #26" (* (^ (+ ?c. (* ?d. (tan (+ ?e. (* ?f. x))))) ?n) (+ ?A. (* ?B. (tan (+ ?e. (* ?f. x))))) (^ (+ ?a. (* ?b. (tan (+ ?e. (* ?f. x))))) -1)) (tan tan tan) 3 (-1))))
