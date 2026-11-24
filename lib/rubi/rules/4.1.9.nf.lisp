(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.9 trig^m (a+b sin^n+c sin^(2 n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.1.9 #5" (^ (+ ?a. (* ?b. (^ (%sin (+ ?d. (* ?e. x))) ?n.)) (* ?c. (^ (%sin (+ ?d. (* ?e. x))) ?n2.))) -1) (%sin %sin +) 0 (-1))
  ("Rubi 4.1.9 #6" (^ (+ ?a. (* ?b. (^ (%cos (+ ?d. (* ?e. x))) ?n.)) (* ?c. (^ (%cos (+ ?d. (* ?e. x))) ?n2.))) -1) (%cos %cos +) 0 (-1))
  ("Rubi 4.1.9 #49" (* (+ ?A (* ?B. (%sin (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (%sin (+ ?d. (* ?e. x)))) (* ?c. (^ (%sin (+ ?d. (* ?e. x))) 2))) -1)) (%sin %sin + %sin +) 2 (2 -1))
  ("Rubi 4.1.9 #50" (* (+ ?A (* ?B. (%cos (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (%cos (+ ?d. (* ?e. x)))) (* ?c. (^ (%cos (+ ?d. (* ?e. x))) 2))) -1)) (%cos %cos + %cos +) 2 (2 -1))))
