(module rubi)
; Rubi 4.17.3.0 — 5 Inverse trig functions/5.3 Inverse tangent/5.3.1 (a+b arctan(c x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "5.3.1" '(
  ("Rubi 5.3.1 #1" (^ (+ ?a. (* ?b. (atan (* ?c. (^ x ?n.))))) ?p.) #t (atan) 0 ())
  ("Rubi 5.3.1 #2" (^ (+ ?a. (* ?b. (acot (* ?c. (^ x ?n.))))) ?p.) #t (acot) 0 ())
  ("Rubi 5.3.1 #3" (^ (+ ?a. (* ?b. (atan (* ?c. (^ x ?n))))) ?p) #t (atan) 0 ())
  ("Rubi 5.3.1 #4" (^ (+ ?a. (* ?b. (acot (* ?c. (^ x ?n))))) ?p) #t (acot) 0 ())
  ("Rubi 5.3.1 #5" (^ (+ ?a. (* ?b. (atan (* ?c. (^ x ?n))))) ?p) #t (atan) 0 ())
  ("Rubi 5.3.1 #6" (^ (+ ?a. (* ?b. (acot (* ?c. (^ x ?n))))) ?p) #t (acot) 0 ())
  ("Rubi 5.3.1 #7" (^ (+ ?a. (* ?b. (atan (* ?c. (^ x ?n))))) ?p) #t (atan) 0 ())
  ("Rubi 5.3.1 #8" (^ (+ ?a. (* ?b. (acot (* ?c. (^ x ?n))))) ?p) #t (acot) 0 ())
  ("Rubi 5.3.1 #9" (^ (+ ?a. (* ?b. (atan (* ?c. (^ x ?n.))))) ?p) #t (atan) 0 ())
  ("Rubi 5.3.1 #10" (^ (+ ?a. (* ?b. (acot (* ?c. (^ x ?n.))))) ?p) #t (acot) 0 ())))
