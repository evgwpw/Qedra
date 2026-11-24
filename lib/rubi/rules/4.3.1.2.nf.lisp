(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.1.2 (d sec)^m (a+b tan)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.3.1.2 #14" (* (^ (* ?d. (%sec (+ ?e. (* ?f. x)))) 3/2) (^ (+ ?a (* ?b. (%tan (+ ?e. (* ?f. x))))) -1/2)) (%tan + %sec) 2 (-1/2 3/2))
  ("Rubi 4.3.1.2 #22" (* (^ (+ ?a (* ?b. (%tan (+ ?e. (* ?f. x))))) 2) (^ (%sec (+ ?e. (* ?f. x))) -1)) (%sec %tan +) 2 (-1 2))
  ("Rubi 4.3.1.2 #24" (* (%sec (+ ?e. (* ?f. x))) (^ (+ ?a (* ?b. (%tan (+ ?e. (* ?f. x))))) -1)) (%tan + %sec) 2 (-1))
  ("Rubi 4.3.1.2 #25" (* (^ (* ?d. (%sec (+ ?e. (* ?f. x)))) ?m) (^ (+ ?a (* ?b. (%tan (+ ?e. (* ?f. x))))) -1)) (%tan + %sec) 2 (-1))
  ("Rubi 4.3.1.2 #26" (* (^ (* ?d. (%sec (+ ?e. (* ?f. x)))) ?m) (^ (+ ?a (* ?b. (%tan (+ ?e. (* ?f. x))))) -1)) (%tan + %sec) 2 (-1))
  ("Rubi 4.3.1.2 #29" (* (^ (* ?d. (%cos (+ ?e. (* ?f. x)))) -3/2) (^ (+ ?a (* ?b. (%tan (+ ?e. (* ?f. x))))) -1/2)) (%tan + %cos) 2 (-1/2 -3/2))))
