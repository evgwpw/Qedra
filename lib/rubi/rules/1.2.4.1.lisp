(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.2 Trinomial products/1.2.4 Improper/1.2.4.1 (a x^q+b x^n+c x^(2 n-q))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.2.4.1" '(
  ("Rubi 1.2.4.1 #1" (^ (+ (* ?a. (^ x ?q.)) (* ?b. (^ x ?n.)) (* ?c. (^ x ?r.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.4.1 #2" (^ (+ (* ?a. (^ x ?q.)) (* ?b. (^ x ?n.)) (* ?c. (^ x ?r.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.4.1 #3" (^ (+ (* ?a. (^ x ?q.)) (* ?b. (^ x ?n.)) (* ?c. (^ x ?r.))) 1/2) #t (+) 0 (1/2))
  ("Rubi 1.2.4.1 #4" (^ (+ (* ?a. (^ x 2)) (* ?b. (^ x ?n.)) (* ?c. (^ x ?r.))) -1/2) #t (+) 0 (2 -1/2))
  ("Rubi 1.2.4.1 #5" (^ (+ (* ?a. (^ x ?q.)) (* ?b. (^ x ?n.)) (* ?c. (^ x ?r.))) -1/2) #t (+) 0 (-1/2))
  ("Rubi 1.2.4.1 #6" (^ (+ (* ?a. (^ x ?q.)) (* ?b. (^ x ?n.)) (* ?c. (^ x ?r.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.4.1 #7" (^ (+ (* ?a. (^ x ?q.)) (* ?b. (^ x ?n.)) (* ?c. (^ x ?r.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.4.1 #8" (^ (+ (* ?a. (^ x ?q.)) (* ?b. (^ x ?n.)) (* ?c. (^ x ?r.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.4.1 #9" (^ (+ (* ?a. (^ x ?q.)) (* ?b. (^ x ?n.)) (* ?c. (^ x ?r.))) ?p) #t (+) 0 ())
  ("Rubi 1.2.4.1 #10" (^ (+ (* ?a. (^ ?u ?q.)) (* ?b. (^ ?u ?n.)) (* ?c. (^ ?u ?r.))) ?p) #t (+) 0 ())))
