(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.5 Secant/4.5.10 (c+d x)^m (a+b sec)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.5.10" '(
  ("Rubi 4.5.10 #1" (* (^ (+ ?c (* ?d x)) ?m) (csc (+ ?e (* ?k Pi) (* ?f (Complex 0 ?fz) x)))) #t (Complex + csc +) 2 ())
  ("Rubi 4.5.10 #2" (* (^ (+ ?c (* ?d x)) ?m) (csc (+ ?e (* ?k Pi) (* ?f x)))) #t (+ csc +) 2 ())
  ("Rubi 4.5.10 #3" (* (^ (+ ?c (* ?d x)) ?m) (csc (+ ?e (* ?f (Complex 0 ?fz) x)))) #t (Complex + csc +) 2 ())
  ("Rubi 4.5.10 #4" (* (^ (+ ?c (* ?d x)) ?m) (csc (+ ?e (* ?f x)))) #t (+ csc +) 2 ())
  ("Rubi 4.5.10 #5" (* (^ (+ ?c (* ?d x)) ?m) (^ (csc (+ ?e (* ?f x))) 2)) #t (+ csc +) 2 (2))
  ("Rubi 4.5.10 #6" (* (+ ?c (* ?d x)) (^ (* ?b (csc (+ ?e (* ?f x)))) ?n)) #t (+ csc +) 2 ())
  ("Rubi 4.5.10 #7" (* (^ (+ ?c (* ?d x)) ?m) (^ (* ?b (csc (+ ?e (* ?f x)))) ?n)) #t (+ csc +) 2 ())
  ("Rubi 4.5.10 #8" (* (+ ?c (* ?d x)) (^ (* ?b (csc (+ ?e (* ?f x)))) ?n)) #t (+ csc +) 2 ())
  ("Rubi 4.5.10 #9" (* (^ (+ ?c (* ?d x)) ?m) (^ (* ?b (csc (+ ?e (* ?f x)))) ?n)) #t (+ csc +) 2 ())
  ("Rubi 4.5.10 #10" (* (^ (+ ?c (* ?d x)) ?m) (^ (* ?b (csc (+ ?e (* ?f x)))) ?n)) #t (+ csc +) 2 ())
  ("Rubi 4.5.10 #11" (* (^ (+ ?c (* ?d x)) ?m) (^ (+ ?a (* ?b (csc (+ ?e (* ?f x))))) ?n)) #t (+ csc + +) 2 ())
  ("Rubi 4.5.10 #12" (* (^ (+ ?c (* ?d x)) ?m) (^ (+ ?a (* ?b (csc (+ ?e (* ?f x))))) ?n)) #t (+ csc + +) 2 ())
  ("Rubi 4.5.10 #13" (* (^ (+ ?c (* ?d x)) ?m) (^ (csc (+ ?e (* ?f x))) ?n)) #t (+ csc +) 2 ())
  ("Rubi 4.5.10 #14" (* (^ (+ ?c (* ?d x)) ?m) (^ (+ ?a (* ?b (csc (+ ?e (* ?f x))))) ?n)) #t (+ csc + +) 2 ())
  ("Rubi 4.5.10 #15" (* (^ ?u ?m) (^ (+ ?a (* ?b (sec ?v))) ?n)) #t (sec +) 2 ())
  ("Rubi 4.5.10 #16" (* (^ ?u ?m) (^ (+ ?a (* ?b (csc ?v))) ?n)) #t (csc +) 2 ())))
