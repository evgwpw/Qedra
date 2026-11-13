(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.5 P(x) (a+b x^2+c x^4)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.2.2.5" '(
  ("Rubi 1.2.2.5 #1" (* ?Pq (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) ?p.)) #t (+) 1 (4 2))
  ("Rubi 1.2.2.5 #2" (* ?Pq (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) ?p)) #t (+) 1 (4 2))
  ("Rubi 1.2.2.5 #3" (* ?Pq (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) ?p)) #t (+) 1 (4 2))
  ("Rubi 1.2.2.5 #4" (* ?Pq (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) ?p.)) #t (+) 1 (4 2))
  ("Rubi 1.2.2.5 #5" (* ?Pq (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) ?p.)) #t (+) 1 (4 2))
  ("Rubi 1.2.2.5 #6" (/ ?Pq (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4)))) #t (+) 0 (4 2))
  ("Rubi 1.2.2.5 #7" (* ?Pq (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) ?p)) #t (+) 1 (4 2))
  ("Rubi 1.2.2.5 #8" (* ?Pq (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) ?p)) #t (+) 1 (4 2))
  ("Rubi 1.2.2.5 #9" (* ?Pq (^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) ?p)) #t (+) 1 (4 2))
  ("Rubi 1.2.2.5 #10" (* ?Pq (^ ?Q4 ?p)) #t () 1 ())))
