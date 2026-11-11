(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.3 Polynomial products/1.3.3 P(x)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.3.3-2" '(
  ("Rubi 1.3.3-2 #1" (* (^ (* ?c x) ?m) ?Pq (^ ?u ?p)) #t () 2 ())
  ("Rubi 1.3.3-2 #2" (* ?Pq (^ ?u ?p)) #t () 1 ())
  ("Rubi 1.3.3-2 #3" (* (^ ?u ?m) ?Pq (^ ?v ?p)) #t () 2 ())
  ("Rubi 1.3.3-2 #4" (* ?Pq (^ ?u ?p)) #t () 1 ())
  ("Rubi 1.3.3-2 #5" (* (^ (* ?d x) ?m) ?Pq (^ ?u ?p)) #t () 2 ())
  ("Rubi 1.3.3-2 #6" (* ?u (^ ?Px ?p) (^ ?Qx ?q)) #t () 2 ())
  ("Rubi 1.3.3-2 #7" (* ?u ?Px (^ ?Qx ?q)) #t () 1 ())
  ("Rubi 1.3.3-2 #8" (^ ?Pn ?p) #t () 0 ())
  ("Rubi 1.3.3-2 #9" (* (^ ?Pn ?p) ?Qx) #t () 1 ())
  ("Rubi 1.3.3-2 #10" (* ?u (^ ?Px ?p)) #t () 1 ())
  ("Rubi 1.3.3-2 #11" (* ?u (^ ?Px ?p)) #t () 1 ())
  ("Rubi 1.3.3-2 #12" (* ?u (^ ?Px ?p)) #t () 1 ())
  ("Rubi 1.3.3-2 #13" (* ?u (^ ?Px ?p)) #t () 1 ())
  ("Rubi 1.3.3-2 #14" (* ?u (^ ?Px ?p)) #t () 1 ())
  ("Rubi 1.3.3-2 #15" (* ?u (^ ?Px ?p)) #t () 1 ())
  ("Rubi 1.3.3-2 #16" (* ?u (^ ?Q6 ?p)) #t () 1 ())
  ("Rubi 1.3.3-2 #17" (* (^ ?Px ?p) ?Fx) #t () 1 ())
  ("Rubi 1.3.3-2 #18" (* (^ (+ (* ?a (^ x ?r)) (* ?b (^ x ?s))) ?p) ?Fx) #t (+) 1 ())
  ("Rubi 1.3.3-2 #19" (* (^ (+ (* ?a (^ x ?r)) (* ?b (^ x ?s)) (* ?c (^ x ?t))) ?p) ?Fx) #t (+) 1 ())
  ("Rubi 1.3.3-2 #20" (* (^ (+ (* ?a (^ x ?r)) (* ?b (^ x ?s)) (* ?c (^ x ?t)) (* ?d (^ x ?q))) ?p) ?Fx) #t (+) 1 ())))
