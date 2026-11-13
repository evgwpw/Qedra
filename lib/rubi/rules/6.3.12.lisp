(module rubi)
; Rubi 4.17.3.0 — 6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.12 (d+e x)^m tanh(a+b x+c x^2)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "6.3.12" '(
  ("Rubi 6.3.12 #1" (^ (tanh (+ ?a. (* ?b. x) (* ?c. (^ x 2)))) ?n.) #t (+ tanh) 0 (2))
  ("Rubi 6.3.12 #2" (^ (coth (+ ?a. (* ?b. x) (* ?c. (^ x 2)))) ?n.) #t (+ coth) 0 (2))
  ("Rubi 6.3.12 #3" (* (+ ?d. (* ?e. x)) (tanh (+ ?a. (* ?b. x) (* ?c. (^ x 2))))) #t (+ tanh) 2 (2))
  ("Rubi 6.3.12 #4" (* (+ ?d. (* ?e. x)) (coth (+ ?a. (* ?b. x) (* ?c. (^ x 2))))) #t (+ coth) 2 (2))
  ("Rubi 6.3.12 #5" (* (^ (+ ?d. (* ?e. x)) ?m.) (^ (tanh (+ ?a. (* ?b. x) (* ?c. (^ x 2)))) ?n.)) #t (+ tanh) 2 (2))
  ("Rubi 6.3.12 #6" (* (^ (+ ?d. (* ?e. x)) ?m.) (^ (coth (+ ?a. (* ?b. x) (* ?c. (^ x 2)))) ?n.)) #t (+ coth) 2 (2))))
