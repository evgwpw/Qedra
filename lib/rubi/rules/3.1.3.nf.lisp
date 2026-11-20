(module rubi)
; Rubi 4.17.3.0 — 3 Logarithms/3.1.3 (d+e x^r)^q (a+b log(c x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 3.1.3 #4" (* (log (* ?c. x)) (^ (+ ?d (* ?e. x)) -1)) (+ log) 2 (-1))
  ("Rubi 3.1.3 #5" (* (+ ?a. (* ?b. (log (* ?c. x)))) (^ (+ ?d (* ?e. x)) -1)) (+ log) 2 (-1))
  ("Rubi 3.1.3 #6" (* (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.) (^ (+ ?d (* ?e. x)) -1)) (+ log) 2 (-1))
  ("Rubi 3.1.3 #7" (* (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.) (^ (+ ?d (* ?e. x)) -2)) (+ log) 2 (-2))
  ("Rubi 3.1.3 #11" (* (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) (^ (+ ?d (* ?e. (^ x 2))) -3/2)) (+ log) 2 (2 -3/2))
  ("Rubi 3.1.3 #13" (* (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) (^ (+ ?d (* ?e. (^ x 2))) -1)) (+ log) 2 (2 -1))
  ("Rubi 3.1.3 #17" (* (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) (^ (+ ?d1 (* ?e1. x)) -1/2) (^ (+ ?d2 (* ?e2. x)) -1/2)) (+ + log) 3 (-1/2 -1/2))))
