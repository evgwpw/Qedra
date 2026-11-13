(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.14 P(x) (c+d x)^m (e+f x)^n (a+b x^2)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.1.2.14" '(
  ("Rubi 1.1.2.14 #1" (* ?Px (^ (+ ?c (* ?d x)) ?m) (^ (+ ?e (* ?f x)) ?n) (^ (+ ?a (* ?b (^ x 2))) ?p)) #t (+ + +) 3 (2))
  ("Rubi 1.1.2.14 #2" (* ?Px (^ (+ ?c (* ?d x)) ?m) (^ (+ ?e (* ?f x)) ?n) (^ (+ ?a (* ?b (^ x 2))) ?p)) #t (+ + +) 3 (2))
  ("Rubi 1.1.2.14 #3" (* ?Px (^ (+ ?c (* ?d x)) ?m) (^ (+ ?e (* ?f x)) ?n) (^ (+ ?a (* ?b (^ x 2))) ?p)) #t (+ + +) 3 (2))))
