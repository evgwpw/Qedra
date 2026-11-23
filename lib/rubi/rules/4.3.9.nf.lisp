(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.9 trig^m (a+b tan^n+c tan^(2 n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.3.9 #5" (^ (+ ?a. (* ?b. (^ (tan (+ ?d. (* ?e. x))) ?n.)) (* ?c. (^ (tan (+ ?d. (* ?e. x))) ?n2.))) -1) (tan tan +) 0 (-1))
  ("Rubi 4.3.9 #6" (^ (+ ?a. (* ?b. (^ (cot (+ ?d. (* ?e. x))) ?n.)) (* ?c. (^ (cot (+ ?d. (* ?e. x))) ?n2.))) -1) (cot cot +) 0 (-1))
  ("Rubi 4.3.9 #31" (* (+ ?A (* ?B. (tan (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (tan (+ ?d. (* ?e. x)))) (* ?c. (^ (tan (+ ?d. (* ?e. x))) 2))) -1)) (tan tan + tan +) 2 (2 -1))
  ("Rubi 4.3.9 #32" (* (+ ?A (* ?B. (cot (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cot (+ ?d. (* ?e. x)))) (* ?c. (^ (cot (+ ?d. (* ?e. x))) 2))) -1)) (cot cot + cot +) 2 (2 -1))))
