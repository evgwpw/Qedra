(module rubi)
; Rubi 4.17.3.0 — 6 Hyperbolic functions/6.1 Hyperbolic sine/6.1.10 (c+d x)^m (a+b sinh)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "6.1.10" '(
  ("Rubi 6.1.10 #1" (* (^ ?u ?m) (^ (+ ?a (* ?b (sinh ?v))) ?n)) #t (sinh +) 2 ())
  ("Rubi 6.1.10 #2" (* (^ ?u ?m) (^ (+ ?a (* ?b (cosh ?v))) ?n)) #t (cosh +) 2 ())))
