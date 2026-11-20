(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.1.3 (g tan)^p (a+b sin)^m.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.1.1.3 #1" (* (^ (* ?g. (tan (+ ?e. (* ?f. x)))) ?p.) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + tan) 2 (-1))
  ("Rubi 4.1.1.3 #10" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (^ (tan (+ ?e. (* ?f. x))) -2)) (tan sin +) 2 (-2))
  ("Rubi 4.1.1.3 #11" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m.) (^ (tan (+ ?e. (* ?f. x))) -2)) (tan sin +) 2 (-2))
  ("Rubi 4.1.1.3 #12" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (^ (tan (+ ?e. (* ?f. x))) -4)) (tan sin +) 2 (-4))
  ("Rubi 4.1.1.3 #13" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (^ (tan (+ ?e. (* ?f. x))) -4)) (tan sin +) 2 (-4))
  ("Rubi 4.1.1.3 #18" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (^ (tan (+ ?e. (* ?f. x))) -2)) (tan sin +) 2 (-2))
  ("Rubi 4.1.1.3 #19" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (^ (tan (+ ?e. (* ?f. x))) -4)) (tan sin +) 2 (-4))
  ("Rubi 4.1.1.3 #20" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (^ (tan (+ ?e. (* ?f. x))) -4)) (tan sin +) 2 (-4))
  ("Rubi 4.1.1.3 #21" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (^ (tan (+ ?e. (* ?f. x))) -6)) (tan sin +) 2 (-6))
  ("Rubi 4.1.1.3 #22" (* (^ (* ?g. (tan (+ ?e. (* ?f. x)))) ?p) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + tan) 2 (-1))
  ("Rubi 4.1.1.3 #23" (* (^ (* ?g. (tan (+ ?e. (* ?f. x)))) ?p) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + tan) 2 (-1))))
