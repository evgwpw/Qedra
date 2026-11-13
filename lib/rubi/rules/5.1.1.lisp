(module rubi)
; Rubi 4.17.3.0 — 5 Inverse trig functions/5.1 Inverse sine/5.1.1 (a+b arcsin(c x))^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "5.1.1" '(
  ("Rubi 5.1.1 #1" (^ (+ ?a. (* ?b. (asin (* ?c. x)))) ?n.) #t (asin) 0 ())
  ("Rubi 5.1.1 #2" (^ (+ ?a. (* ?b. (acos (* ?c. x)))) ?n.) #t (acos) 0 ())
  ("Rubi 5.1.1 #3" (^ (+ ?a. (* ?b. (asin (* ?c. x)))) ?n) #t (asin) 0 ())
  ("Rubi 5.1.1 #4" (^ (+ ?a. (* ?b. (acos (* ?c. x)))) ?n) #t (acos) 0 ())
  ("Rubi 5.1.1 #5" (^ (+ ?a. (* ?b. (asin (* ?c. x)))) ?n) #t (asin) 0 ())
  ("Rubi 5.1.1 #6" (^ (+ ?a. (* ?b. (acos (* ?c. x)))) ?n) #t (acos) 0 ())))
