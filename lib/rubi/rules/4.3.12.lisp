(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.12 (d+e x)^m tan(a+b x+c x^2)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.3.12" '(
  ("Rubi 4.3.12 #1" (^ (tan (+ ?a. (* ?b. x) (* ?c. (^ x 2)))) ?n.) #t (+ tan) 0 (2))
  ("Rubi 4.3.12 #2" (^ (cot (+ ?a. (* ?b. x) (* ?c. (^ x 2)))) ?n.) #t (+ cot) 0 (2))
  ("Rubi 4.3.12 #3" (* (+ ?d (* ?e. x)) (tan (+ ?a. (* ?b. x) (* ?c. (^ x 2))))) #t (+ tan +) 2 (2))
  ("Rubi 4.3.12 #4" (* (+ ?d (* ?e. x)) (cot (+ ?a. (* ?b. x) (* ?c. (^ x 2))))) #t (+ cot +) 2 (2))
  ("Rubi 4.3.12 #5" (* (+ ?d. (* ?e. x)) (tan (+ ?a. (* ?b. x) (* ?c. (^ x 2))))) #t (+ tan) 2 (2))
  ("Rubi 4.3.12 #6" (* (+ ?d. (* ?e. x)) (cot (+ ?a. (* ?b. x) (* ?c. (^ x 2))))) #t (+ cot) 2 (2))
  ("Rubi 4.3.12 #7" (* (^ (+ ?d. (* ?e. x)) ?m.) (^ (tan (+ ?a. (* ?b. x) (* ?c. (^ x 2)))) ?n.)) #t (+ tan) 2 (2))
  ("Rubi 4.3.12 #8" (* (^ (+ ?d. (* ?e. x)) ?m.) (^ (cot (+ ?a. (* ?b. x) (* ?c. (^ x 2)))) ?n.)) #t (+ cot) 2 (2))))
