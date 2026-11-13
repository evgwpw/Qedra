(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.11 (e x)^m (a+b x^n)^p sin.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.1.11" '(
  ("Rubi 4.1.11 #1" (* (^ (+ ?a (* ?b (^ x ?n))) ?p) (sin (+ ?c (* ?d x)))) #t (+ sin +) 2 ())
  ("Rubi 4.1.11 #2" (* (^ (+ ?a (* ?b (^ x ?n))) ?p) (cos (+ ?c (* ?d x)))) #t (+ cos +) 2 ())
  ("Rubi 4.1.11 #3" (* (^ (+ ?a (* ?b (^ x ?n))) ?p) (sin (+ ?c (* ?d x)))) #t (+ sin +) 2 ())
  ("Rubi 4.1.11 #4" (* (^ (+ ?a (* ?b (^ x ?n))) ?p) (cos (+ ?c (* ?d x)))) #t (+ cos +) 2 ())
  ("Rubi 4.1.11 #5" (* (^ (+ ?a (* ?b (^ x ?n))) ?p) (sin (+ ?c (* ?d x)))) #t (+ sin +) 2 ())
  ("Rubi 4.1.11 #6" (* (^ (+ ?a (* ?b (^ x ?n))) ?p) (cos (+ ?c (* ?d x)))) #t (+ cos +) 2 ())
  ("Rubi 4.1.11 #7" (* (^ (+ ?a (* ?b (^ x ?n))) ?p) (sin (+ ?c (* ?d x)))) #t (+ sin +) 2 ())
  ("Rubi 4.1.11 #8" (* (^ (+ ?a (* ?b (^ x ?n))) ?p) (cos (+ ?c (* ?d x)))) #t (+ cos +) 2 ())
  ("Rubi 4.1.11 #9" (* (^ (+ ?a (* ?b (^ x ?n))) ?p) (sin (+ ?c (* ?d x)))) #t (+ sin +) 2 ())
  ("Rubi 4.1.11 #10" (* (^ (+ ?a (* ?b (^ x ?n))) ?p) (cos (+ ?c (* ?d x)))) #t (+ cos +) 2 ())
  ("Rubi 4.1.11 #11" (* (^ (* ?e x) ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (sin (+ ?c (* ?d x)))) #t (+ sin +) 3 ())
  ("Rubi 4.1.11 #12" (* (^ (* ?e x) ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (cos (+ ?c (* ?d x)))) #t (+ cos +) 3 ())
  ("Rubi 4.1.11 #13" (* (^ (* ?e x) ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (sin (+ ?c (* ?d x)))) #t (+ sin +) 3 ())
  ("Rubi 4.1.11 #14" (* (^ (* ?e x) ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (cos (+ ?c (* ?d x)))) #t (+ cos +) 3 ())
  ("Rubi 4.1.11 #15" (* (^ x ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (sin (+ ?c (* ?d x)))) #t (+ sin +) 3 ())
  ("Rubi 4.1.11 #16" (* (^ x ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (cos (+ ?c (* ?d x)))) #t (+ cos +) 3 ())
  ("Rubi 4.1.11 #17" (* (^ x ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (sin (+ ?c (* ?d x)))) #t (+ sin +) 3 ())
  ("Rubi 4.1.11 #18" (* (^ x ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (cos (+ ?c (* ?d x)))) #t (+ cos +) 3 ())
  ("Rubi 4.1.11 #19" (* (^ x ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (sin (+ ?c (* ?d x)))) #t (+ sin +) 3 ())
  ("Rubi 4.1.11 #20" (* (^ x ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (cos (+ ?c (* ?d x)))) #t (+ cos +) 3 ())
  ("Rubi 4.1.11 #21" (* (^ (* ?e x) ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (sin (+ ?c (* ?d x)))) #t (+ sin +) 3 ())
  ("Rubi 4.1.11 #22" (* (^ (* ?e x) ?m) (^ (+ ?a (* ?b (^ x ?n))) ?p) (cos (+ ?c (* ?d x)))) #t (+ cos +) 3 ())))
