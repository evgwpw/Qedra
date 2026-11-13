(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.2 (d x)^m (a+b arccosh(c x))^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "7.2.2" '(
  ("Rubi 7.2.2 #1" (/ (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n) x) #t (acosh +) 0 ())
  ("Rubi 7.2.2 #2" (* (^ (* ?d x) ?m) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh +) 2 ())
  ("Rubi 7.2.2 #3" (* (^ x ?m) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh +) 2 ())
  ("Rubi 7.2.2 #4" (* (^ x ?m) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh +) 2 ())
  ("Rubi 7.2.2 #5" (* (^ x ?m) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh +) 2 ())
  ("Rubi 7.2.2 #6" (* (^ x ?m) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh +) 2 ())
  ("Rubi 7.2.2 #7" (* (^ (* ?d x) ?m) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh +) 2 ())))
