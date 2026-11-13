(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.1 (a+b arctanh(c x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "7.3.1" '(
  ("Rubi 7.3.1 #1" (^ (+ ?a (* ?b (atanh (* ?c (^ x ?n))))) ?p) #t (atanh +) 0 ())
  ("Rubi 7.3.1 #2" (^ (+ ?a (* ?b (acoth (* ?c (^ x ?n))))) ?p) #t (acoth +) 0 ())
  ("Rubi 7.3.1 #3" (^ (+ ?a (* ?b (atanh (* ?c (^ x ?n))))) ?p) #t (atanh +) 0 ())
  ("Rubi 7.3.1 #4" (^ (+ ?a (* ?b (acoth (* ?c (^ x ?n))))) ?p) #t (acoth +) 0 ())
  ("Rubi 7.3.1 #5" (^ (+ ?a (* ?b (atanh (* ?c (^ x ?n))))) ?p) #t (atanh +) 0 ())
  ("Rubi 7.3.1 #6" (^ (+ ?a (* ?b (acoth (* ?c (^ x ?n))))) ?p) #t (acoth +) 0 ())
  ("Rubi 7.3.1 #7" (^ (+ ?a (* ?b (atanh (* ?c (^ x ?n))))) ?p) #t (atanh +) 0 ())
  ("Rubi 7.3.1 #8" (^ (+ ?a (* ?b (acoth (* ?c (^ x ?n))))) ?p) #t (acoth +) 0 ())
  ("Rubi 7.3.1 #9" (^ (+ ?a (* ?b (atanh (* ?c (^ x ?n))))) ?p) #t (atanh +) 0 ())
  ("Rubi 7.3.1 #10" (^ (+ ?a (* ?b (acoth (* ?c (^ x ?n))))) ?p) #t (acoth +) 0 ())))
