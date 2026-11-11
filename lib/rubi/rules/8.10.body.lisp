(module rubi)
; Rubi 4.17.3.0 — 8 Special functions/8.10 Bessel functions.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Тела правил: ("id" условие правая-часть); читаются лениво (rubi-load-bodies).
(rubi-bodies-data '(
  ("Rubi 8.10 #1" (rubi::rubi-freeq (list ?a ?b) (quote x)) (/ (- (bessel-j 0 (+ a (* b (quote x))))) b))
  ("Rubi 8.10 #2" (and (rubi::rubi-freeq (list ?a ?b) (quote x)) (rubi::rubi-igtq (/ (- ?n 1) 2) 0)) (+ (/ (* (- 2) (bessel-j (- n 1) (+ a (* b (quote x))))) b) (rubi::rubi-int (bessel-j (- n 2) (+ a (* b (quote x)))) (bessel-j (- n 2) (+ a (* b (quote x)))) (quote x))))
  ("Rubi 8.10 #3" (rubi::rubi-freeq (list ?a ?b ?n) (quote x)) (/ (* (^ (+ a (* b (quote x))) (+ n 1)) (rubi::rubi-hypergeometric-pfq (list (/ (+ n 1) 2)) (list (/ (+ n 3) 2) (+ n 1)) (* (/ (- 1) 4) (^ (+ a (* b (quote x))) 2)))) (* (^ 2 n) b (gamma (+ n 2)))))))
