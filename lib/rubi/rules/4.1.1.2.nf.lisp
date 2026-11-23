(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.1.2 (g cos)^p (a+b sin)^m.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.1.1.2 #16" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + cos) 2 (-1))
  ("Rubi 4.1.1.2 #17" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + cos) 2 (-1))
  ("Rubi 4.1.1.2 #19" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) 3/2) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1/2)) (sin + cos) 2 (-1/2 3/2))))
