(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.2 (d x)^m (a+b arcsinh(c x))^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "7.1.2" '(
  ("Rubi 7.1.2 #1" (/ (^ (+ ?a (* ?b (asinh (* ?c x)))) ?n) x) #t (asinh +) 0 ())
  ("Rubi 7.1.2 #2" (* (^ (* ?d x) ?m) (^ (+ ?a (* ?b (asinh (* ?c x)))) ?n)) #t (asinh +) 2 ())
  ("Rubi 7.1.2 #3" (* (^ x ?m) (^ (+ ?a (* ?b (asinh (* ?c x)))) ?n)) #t (asinh +) 2 ())
  ("Rubi 7.1.2 #4" (* (^ x ?m) (^ (+ ?a (* ?b (asinh (* ?c x)))) ?n)) #t (asinh +) 2 ())
  ("Rubi 7.1.2 #5" (* (^ x ?m) (^ (+ ?a (* ?b (asinh (* ?c x)))) ?n)) #t (asinh +) 2 ())
  ("Rubi 7.1.2 #6" (* (^ x ?m) (^ (+ ?a (* ?b (asinh (* ?c x)))) ?n)) #t (asinh +) 2 ())
  ("Rubi 7.1.2 #7" (* (^ (* ?d x) ?m) (^ (+ ?a (* ?b (asinh (* ?c x)))) ?n)) #t (asinh +) 2 ())))
