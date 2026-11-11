(module rubi)
; Rubi 4.17.3.0 — 8 Special functions/8.7 Zeta function.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Тела правил: ("id" условие правая-часть); читаются лениво (rubi-load-bodies).
(rubi-bodies-data '(
  ("Rubi 8.7 #1" (rubi::rubi-freeq (list ?a ?b) (quote x)) (rubi::rubi-int (rubi::rubi-poly-gamma 1 (+ a (* b (quote x)))) (rubi::rubi-poly-gamma 1 (+ a (* b (quote x)))) (quote x)))
  ("Rubi 8.7 #2" (and (and (rubi::rubi-freeq (list ?a ?b ?s) (quote x)) (rubi::rubi-neq ?s 1)) (rubi::rubi-neq ?s 2)) (/ (- (zeta (- s 1) (+ a (* b (quote x))))) (* b (- s 1))))
  ("Rubi 8.7 #3" (and (rubi::rubi-freeq (list ?a ?b ?c ?d) (quote x)) (rubi::rubi-rationalq ?m)) (rubi::rubi-int (* (^ (+ c (* d (quote x))) m) (rubi::rubi-poly-gamma 1 (+ a (* b (quote x))))) (* (^ (+ c (* d (quote x))) m) (rubi::rubi-poly-gamma 1 (+ a (* b (quote x))))) (quote x)))
  ("Rubi 8.7 #4" (and (and (and (rubi::rubi-freeq (list ?a ?b ?c ?d ?s) (quote x)) (rubi::rubi-neq ?s 1)) (rubi::rubi-neq ?s 2)) (rubi::rubi-gtq ?m 0)) (+ (/ (* (^ (- (+ c (* d (quote x)))) m) (zeta (- s 1) (+ a (* b (quote x))))) (* b (- s 1))) (* (/ (* d m) (* b (- s 1))) (rubi::rubi-int (* (^ (+ c (* d (quote x))) (- m 1)) (zeta (- s 1) (+ a (* b (quote x))))) (* (^ (+ c (* d (quote x))) (- m 1)) (zeta (- s 1) (+ a (* b (quote x))))) (quote x)))))
  ("Rubi 8.7 #5" (and (and (and (rubi::rubi-freeq (list ?a ?b ?c ?d ?s) (quote x)) (rubi::rubi-neq ?s 1)) (rubi::rubi-neq ?s 2)) (rubi::rubi-ltq ?m (- 1))) (+ (/ (* (^ (+ c (* d (quote x))) (+ m 1)) (zeta s (+ a (* b (quote x))))) (* d (+ m 1))) (* (/ (* b s) (* d (+ m 1))) (rubi::rubi-int (* (^ (+ c (* d (quote x))) (+ m 1)) (zeta (+ s 1) (+ a (* b (quote x))))) (* (^ (+ c (* d (quote x))) (+ m 1)) (zeta (+ s 1) (+ a (* b (quote x))))) (quote x)))))))
