(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.1 (a+b x)^m.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.1.1.1" '(
  ("Rubi 1.1.1.1 #1" (/ 1 x) #f () 0 ())
  ("Rubi 1.1.1.1 #2" (^ x ?m) #t () 0 ())
  ("Rubi 1.1.1.1 #3" (/ 1 (+ ?a (* ?b x))) #t (+) 0 ())
  ("Rubi 1.1.1.1 #4" (^ (+ ?a (* ?b x)) ?m) #t (+) 0 ())
  ("Rubi 1.1.1.1 #5" (^ (+ ?a (* ?b ?u)) ?m) #t (+) 0 ())))
