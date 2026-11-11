(module rubi)
; Rubi 4.17.3.0 — 6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.12 (d+e x)^m tanh(a+b x+c x^2)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Тела правил: ("id" условие правая-часть); читаются лениво (rubi-load-bodies).
(rubi-bodies-data '(
  ("Rubi 6.3.12 #1" (rubi::rubi-freeq (list ?a ?b ?c ?n) (quote x)) (rubi::rubi-integral (^ (tanh (+ a (* b (quote x)) (* c (^ (quote x) 2)))) n) (quote x)))
  ("Rubi 6.3.12 #2" (rubi::rubi-freeq (list ?a ?b ?c ?n) (quote x)) (rubi::rubi-integral (^ (coth (+ a (* b (quote x)) (* c (^ (quote x) 2)))) n) (quote x)))
  ("Rubi 6.3.12 #3" (rubi::rubi-freeq (list ?a ?b ?c ?d ?e) (quote x)) (+ (/ (* e (log (cosh (+ a (* b (quote x)) (* c (^ (quote x) 2)))))) (* 2 c)) (* (/ (- (* 2 c d) (* b e)) (* 2 c)) (rubi::rubi-int (tanh (+ a (* b (quote x)) (* c (^ (quote x) 2)))) (tanh (+ a (* b (quote x)) (* c (^ (quote x) 2)))) (quote x)))))
  ("Rubi 6.3.12 #4" (rubi::rubi-freeq (list ?a ?b ?c ?d ?e) (quote x)) (+ (/ (* e (log (sinh (+ a (* b (quote x)) (* c (^ (quote x) 2)))))) (* 2 c)) (* (/ (- (* 2 c d) (* b e)) (* 2 c)) (rubi::rubi-int (coth (+ a (* b (quote x)) (* c (^ (quote x) 2)))) (coth (+ a (* b (quote x)) (* c (^ (quote x) 2)))) (quote x)))))
  ("Rubi 6.3.12 #5" (rubi::rubi-freeq (list ?a ?b ?c ?d ?e ?m ?n) (quote x)) (rubi::rubi-integral (* (^ (+ d (* e (quote x))) m) (^ (tanh (+ a (* b (quote x)) (* c (^ (quote x) 2)))) n)) (quote x)))
  ("Rubi 6.3.12 #6" (rubi::rubi-freeq (list ?a ?b ?c ?d ?e ?m ?n) (quote x)) (rubi::rubi-integral (* (^ (+ d (* e (quote x))) m) (^ (coth (+ a (* b (quote x)) (* c (^ (quote x) 2)))) n)) (quote x)))))
