(module rubi)
; Rubi 4.17.3.0 — 3 Logarithms/3.1.2 (d x)^m (a+b log(c x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "3.1.2" '(
  ("Rubi 3.1.2 #1" (/ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) x) #t (log) 0 ())
  ("Rubi 3.1.2 #2" (/ (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.) x) #t (log) 0 ())
  ("Rubi 3.1.2 #3" (* (^ (* ?d. x) ?m.) (+ ?a. (* ?b. (log (* ?c. (^ x ?n.)))))) #t (log) 2 ())
  ("Rubi 3.1.2 #4" (* (^ (* ?d. x) ?m.) (+ ?a. (* ?b. (log (* ?c. (^ x ?n.)))))) #t (log) 2 ())
  ("Rubi 3.1.2 #5" (* (^ (* ?d. x) ?m.) (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.)) #t (log) 2 ())
  ("Rubi 3.1.2 #6" (* (^ (* ?d. x) ?m.) (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p)) #t (log) 2 ())
  ("Rubi 3.1.2 #7" (/ (^ x ?m.) (log (* ?c. (^ x ?n)))) #t (log) 0 ())
  ("Rubi 3.1.2 #8" (/ (^ (* ?d x) ?m.) (log (* ?c. (^ x ?n)))) #t (log) 0 ())
  ("Rubi 3.1.2 #9" (* (^ x ?m.) (^ (+ ?a. (* ?b. (log (* ?c. x)))) ?p)) #t (log) 2 ())
  ("Rubi 3.1.2 #10" (* (^ (* ?d. x) ?m.) (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p)) #t (log) 2 ())
  ("Rubi 3.1.2 #11" (* (^ (* ?d. (^ x ?q)) ?m) (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.)) #t (log) 2 ())
  ("Rubi 3.1.2 #12" (* (^ (* ?d1. (^ x ?q1)) ?m1) (^ (* ?d2. (^ x ?q2)) ?m2) (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.)) #t (log) 3 ())))
