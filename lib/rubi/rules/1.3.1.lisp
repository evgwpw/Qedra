(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.3 Miscellaneous/1.3.1 P(x)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.3.1" '(
  ("Rubi 1.3.1 #1" (* ?u (^ ?P ?p) (^ ?Q ?q)) #t () 2 ())
  ("Rubi 1.3.1 #2" (* ?u ?P (^ ?Q ?q)) #t () 1 ())
  ("Rubi 1.3.1 #3" (* ?u (^ ?P ?p)) #t () 1 ())
  ("Rubi 1.3.1 #4" (^ ?P ?p) #t () 0 ())
  ("Rubi 1.3.1 #5" (^ ?P ?p) #t () 0 ())
  ("Rubi 1.3.1 #6" (^ ?P ?p) #t () 0 ())
  ("Rubi 1.3.1 #7" (^ (+ ?a (* ?b x) (* ?c (^ x 2)) (* ?d (^ x 3))) ?p) #t (+) 0 (3 2))
  ("Rubi 1.3.1 #8" (^ ?P ?p) #t () 0 ())
  ("Rubi 1.3.1 #9" (^ ?P ?p) #t () 0 ())
  ("Rubi 1.3.1 #10" (^ (+ ?a (* ?b x) (* ?d (^ x 3))) ?p) #t (+) 0 (3))
  ("Rubi 1.3.1 #11" (^ (+ ?a (* ?b x) (* ?d (^ x 3))) ?p) #t (+) 0 (3))
  ("Rubi 1.3.1 #12" (^ (+ ?a (* ?b x) (* ?d (^ x 3))) ?p) #t (+) 0 (3))
  ("Rubi 1.3.1 #13" (^ (+ ?a (* ?b x) (* ?d (^ x 3))) ?p) #t (+) 0 (3))
  ("Rubi 1.3.1 #14" (^ ?P3 ?p) #t () 0 ())
  ("Rubi 1.3.1 #15" (^ ?P4 ?p) #t () 0 ())
  ("Rubi 1.3.1 #16" (^ ?P4 ?p) #t () 0 ())
  ("Rubi 1.3.1 #17" (^ ?Q6 ?p) #t () 0 ())))
