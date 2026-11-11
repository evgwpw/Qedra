(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.1 Binomial products/1.1.2 Quadratic/1.1.2.x P(x) (a+b x^2)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.1.2.x" '(
  ("Rubi 1.1.2.x #1" (* ?Pq (^ (+ ?a (* ?b (^ x 2))) ?p)) #t (+) 1 (2))
  ("Rubi 1.1.2.x #2" (* ?Pq (^ (+ ?a (* ?b (^ x 2))) ?p)) #t (+) 1 (2))
  ("Rubi 1.1.2.x #3" (* ?Px (^ (+ ?a (* ?b (^ x 2))) ?p)) #t (+) 1 (2))
  ("Rubi 1.1.2.x #4" (* ?Pq (^ (+ ?a (* ?b (^ x 2))) ?p)) #t (+) 1 (2))
  ("Rubi 1.1.2.x #5" (* ?Pq (^ (+ ?a (* ?b (^ x 2))) ?p)) #t (+) 1 (2))
  ("Rubi 1.1.2.x #6" (* ?Pq (^ (+ ?a (* ?b (^ x 2))) ?p)) #t (+) 1 (2))))
