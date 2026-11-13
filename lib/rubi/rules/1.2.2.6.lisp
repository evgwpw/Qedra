(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.2 Trinomial products/1.2.2 Quartic/1.2.2.6 P(x) (d x)^m (a+b x^2+c x^4)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.2.2.6" '(
  ("Rubi 1.2.2.6 #1" (* (^ (* ?d x) ?m) ?Pq (^ (+ ?a (* ?b (^ x 2)) (* ?c (^ x 4))) ?p)) #t (+) 2 (4 2))
  ("Rubi 1.2.2.6 #2" (* (^ x ?m) ?Pq (^ (+ ?a (* ?b (^ x 2)) (* ?c (^ x 4))) ?p)) #t (+) 2 (4 2))
  ("Rubi 1.2.2.6 #3" (* (^ (* ?d x) ?m) ?Pq (^ (+ ?a (* ?b (^ x 2)) (* ?c (^ x 4))) ?p)) #t (+) 2 (4 2))
  ("Rubi 1.2.2.6 #4" (* (^ (* ?d x) ?m) ?Pq (^ (+ ?a (* ?b (^ x 2)) (* ?c (^ x 4))) ?p)) #t (+) 2 (4 2))
  ("Rubi 1.2.2.6 #5" (* (^ (* ?d x) ?m) ?Pq (^ (+ ?a (* ?b (^ x 2)) (* ?c (^ x 4))) ?p)) #t (+) 2 (4 2))
  ("Rubi 1.2.2.6 #6" (* (^ (* ?d x) ?m) ?Pq (^ (+ ?a (* ?b (^ x 2)) (* ?c (^ x 4))) ?p)) #t (+) 2 (4 2))
  ("Rubi 1.2.2.6 #7" (* (^ x ?m) ?Pq (^ (+ ?a (* ?b (^ x 2)) (* ?c (^ x 4))) ?p)) #t (+) 2 (4 2))
  ("Rubi 1.2.2.6 #8" (* (^ x ?m) ?Pq (^ (+ ?a (* ?b (^ x 2)) (* ?c (^ x 4))) ?p)) #t (+) 2 (4 2))
  ("Rubi 1.2.2.6 #9" (* (^ (* ?d x) ?m) ?Pq (^ (+ ?a (* ?b (^ x 2)) (* ?c (^ x 4))) ?p)) #t (+) 2 (4 2))))
