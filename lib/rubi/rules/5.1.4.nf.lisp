(module rubi)
; Rubi 4.17.3.0 — 5 Inverse trig functions/5.1 Inverse sine/5.1.4 (f x)^m (d+e x^2)^p (a+b arcsin(c x))^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 5.1.4 #1" (* x (^ (+ ?a. (* ?b. (asin (* ?c. x)))) ?n.) (^ (+ ?d (* ?e. (^ x 2))) -1)) (+ asin) 3 (2 -1))
  ("Rubi 5.1.4 #2" (* x (^ (+ ?a. (* ?b. (acos (* ?c. x)))) ?n.) (^ (+ ?d (* ?e. (^ x 2))) -1)) (+ acos) 3 (2 -1))
  ("Rubi 5.1.4 #5" (* (^ (+ ?a. (* ?b. (asin (* ?c. x)))) ?n.) (^ x -1) (^ (+ ?d (* ?e. (^ x 2))) -1)) (+ asin) 3 (2 -1 -1))
  ("Rubi 5.1.4 #6" (* (^ (+ ?a. (* ?b. (acos (* ?c. x)))) ?n.) (^ x -1) (^ (+ ?d (* ?e. (^ x 2))) -1)) (+ acos) 3 (2 -1 -1))
  ("Rubi 5.1.4 #9" (* (^ (+ ?d (* ?e. (^ x 2))) ?p.) (+ ?a. (* ?b. (asin (* ?c. x)))) (^ x -1)) (asin +) 3 (-1 2))
  ("Rubi 5.1.4 #10" (* (^ (+ ?d (* ?e. (^ x 2))) ?p.) (+ ?a. (* ?b. (acos (* ?c. x)))) (^ x -1)) (acos +) 3 (-1 2))))
