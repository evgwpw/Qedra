(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.2 Trinomial products/1.2.3 General/1.2.3.1 (a+b x^n+c x^(2 n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.2.3.1" '(
  ("Rubi 1.2.3.1 #1" (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) ?p.) #t (+) 0 ())
  ("Rubi 1.2.3.1 #2" (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.3.1 #3" (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.3.1 #4" (^ (+ ?a (* ?b. (^ x ?n.)) (* ?c. (^ x ?n2.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.3.1 #5" (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.3.1 #6" (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.3.1 #7" (/ 1 (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2)))) #t (+) 0 ())
  ("Rubi 1.2.3.1 #8" (/ 1 (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2)))) #t (+) 0 ())
  ("Rubi 1.2.3.1 #9" (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.3.1 #10" (^ (+ ?a (* ?b. (^ ?u ?n)) (* ?c. (^ ?u ?n2.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.3.1 #11" (^ (+ ?a (* ?b. (^ x ?mn)) (* ?c. (^ x ?n.))) ?p.) #t (+) 0 ())
  ("Rubi 1.2.3.1 #12" (^ (+ ?a (* ?b. (^ x ?mn)) (* ?c. (^ x ?n.))) ?p) #t (+) 0 ())))
