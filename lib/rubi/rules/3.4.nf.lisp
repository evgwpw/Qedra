(module rubi)
; Rubi 4.17.3.0 — 3 Logarithms/3.4 u (a+b log(c (d+e x^m)^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 3.4 #3" (^ (+ ?a. (* ?b. (log (* ?c. (^ (+ ?d (* ?e. (^ x -1))) ?p.))))) ?q) (+ log) 0 (-1))
  ("Rubi 3.4 #16" (* (+ ?a. (* ?b. (log (* ?c. (^ (+ ?d (* ?e. (^ x ?n))) ?p.))))) (^ (+ ?f. (* ?g. x)) -1)) (+ log) 2 (-1))
  ("Rubi 3.4 #24" (* (+ ?a. (* ?b. (log (* ?c. (^ (+ ?d (* ?e. (^ x ?n))) ?p.))))) (^ (+ ?f (* ?g. (^ x 2))) -1)) (+ + log) 2 (2 -1))
  ("Rubi 3.4 #36" (* (^ (log (* ?f. (^ x ?q.))) ?m.) (+ ?a. (* ?b. (log (* ?c. (^ (+ ?d (* ?e. (^ x ?n))) ?p.))))) (^ x -1)) (+ log log) 3 (-1))))
