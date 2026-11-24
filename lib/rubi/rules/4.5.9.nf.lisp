(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.5 Secant/4.5.9 trig^m (a+b sec^n+c sec^(2 n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.5.9 #5" (^ (+ ?a. (* ?b. (^ (%sec (+ ?d. (* ?e. x))) ?n.)) (* ?c. (^ (%sec (+ ?d. (* ?e. x))) ?n2.))) -1) (%sec %sec +) 0 (-1))
  ("Rubi 4.5.9 #6" (^ (+ ?a. (* ?b. (^ (%csc (+ ?d. (* ?e. x))) ?n.)) (* ?c. (^ (%csc (+ ?d. (* ?e. x))) ?n2.))) -1) (%csc %csc +) 0 (-1))
  ("Rubi 4.5.9 #25" (* (+ ?A (* ?B. (%sec (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (%sec (+ ?d. (* ?e. x)))) (* ?c. (^ (%sec (+ ?d. (* ?e. x))) 2))) -1)) (%sec %sec + %sec +) 2 (2 -1))
  ("Rubi 4.5.9 #26" (* (+ ?A (* ?B. (%csc (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (%csc (+ ?d. (* ?e. x)))) (* ?c. (^ (%csc (+ ?d. (* ?e. x))) 2))) -1)) (%csc %csc + %csc +) 2 (2 -1))))
