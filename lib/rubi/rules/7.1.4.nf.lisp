(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.4 (f x)^m (d+e x^2)^p (a+b arcsinh(c x))^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 7.1.4 #1" (* x (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.) (^ (+ ?d (* ?e. (^ x 2))) -1)) (+ asinh) 3 (2 -1))
  ("Rubi 7.1.4 #3" (* (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.) (^ x -1) (^ (+ ?d (* ?e. (^ x 2))) -1)) (+ asinh) 3 (2 -1 -1))
  ("Rubi 7.1.4 #5" (* (^ (+ ?d (* ?e. (^ x 2))) ?p.) (+ ?a. (* ?b. (asinh (* ?c. x)))) (^ x -1)) (asinh +) 3 (-1 2))))
