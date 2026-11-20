(module rubi)
; Rubi 4.17.3.0 — 5 Inverse trig functions/5.3 Inverse tangent/5.3.2 (d x)^m (a+b arctan(c x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 5.3.2 #1" (* (+ ?a. (* ?b. (atan (* ?c. x)))) (^ x -1)) (atan) 2 (-1))
  ("Rubi 5.3.2 #2" (* (+ ?a. (* ?b. (acot (* ?c. x)))) (^ x -1)) (acot) 2 (-1))
  ("Rubi 5.3.2 #3" (* (^ (+ ?a. (* ?b. (atan (* ?c. x)))) ?p) (^ x -1)) (atan) 2 (-1))
  ("Rubi 5.3.2 #4" (* (^ (+ ?a. (* ?b. (acot (* ?c. x)))) ?p) (^ x -1)) (acot) 2 (-1))
  ("Rubi 5.3.2 #5" (* (^ (+ ?a. (* ?b. (atan (* ?c. (^ x ?n))))) ?p.) (^ x -1)) (atan) 2 (-1))
  ("Rubi 5.3.2 #6" (* (^ (+ ?a. (* ?b. (acot (* ?c. (^ x ?n))))) ?p.) (^ x -1)) (acot) 2 (-1))))
