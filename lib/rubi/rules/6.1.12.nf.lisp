(module rubi)
; Rubi 4.17.3.0 — 6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.12 (e x)^m (a+b sinh(c+d x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 6.1.12 #19" (* (sinh (* ?d. (^ x ?n))) (^ x -1)) (sinh) 2 (-1))
  ("Rubi 6.1.12 #20" (* (cosh (* ?d. (^ x ?n))) (^ x -1)) (cosh) 2 (-1))
  ("Rubi 6.1.12 #21" (* (sinh (+ ?c (* ?d. (^ x ?n)))) (^ x -1)) (+ sinh) 2 (-1))
  ("Rubi 6.1.12 #22" (* (cosh (+ ?c (* ?d. (^ x ?n)))) (^ x -1)) (+ cosh) 2 (-1))))
