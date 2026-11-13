(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.2 Trinomial products/1.2.1 Quadratic/1.2.1.8 P(x) (d+e x)^m (f+g x)^n (a+b x+c x^2)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.2.1.8-2" '(
  ("Rubi 1.2.1.8-2 #1" (* ?Px (^ (+ ?d. (* ?e. x)) ?m.) (^ (+ ?f. (* ?g. x)) ?n.) (^ (+ ?a. (* ?b. x) (* ?c. (^ x 2))) ?p.)) #t (+) 3 (2))
  ("Rubi 1.2.1.8-2 #2" (* ?Px (^ (+ ?d. (* ?e. x)) ?m.) (^ (+ ?f. (* ?g. x)) ?n.) (^ (+ ?a. (* ?b. x) (* ?c. (^ x 2))) ?p.)) #t (+) 3 (2))
  ("Rubi 1.2.1.8-2 #3" (* ?Px (^ (+ ?d. (* ?e. x)) ?m.) (^ (+ ?f. (* ?g. x)) ?n.) (^ (+ ?a. (* ?b. x) (* ?c. (^ x 2))) ?p.)) #t (+) 3 (2))))
