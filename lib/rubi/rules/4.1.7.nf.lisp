(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.7 (d trig)^m (a+b (c sin)^n)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.1.7 #3" (* (+ ?A. (* ?B. (^ (sin (+ ?e. (* ?f. x))) 2))) (^ (+ ?a (* ?b. (^ (sin (+ ?e. (* ?f. x))) 2))) -1)) (sin + sin) 2 (2 -1 2))
  ("Rubi 4.1.7 #13" (^ (+ ?a (* ?b. (^ (sin (+ ?e. (* ?f. x))) 2))) -1) (sin +) 0 (2 -1))
  ("Rubi 4.1.7 #43" (^ (+ ?a (* ?b. (^ (sin (+ ?e. (* ?f. x))) ?n))) -1) (sin +) 0 (-1))
  ("Rubi 4.1.7 #58" (* (^ (cos (+ ?e. (* ?f. x))) ?m) (^ (+ ?a (* ?b. (^ (sin (+ ?e. (* ?f. x))) ?n))) -1)) (sin + cos) 2 (-1))))
