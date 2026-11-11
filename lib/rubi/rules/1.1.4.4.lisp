(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.1 Binomial products/1.1.4 Improper/1.1.4.4 P(x) (c x)^m (a x^j+b x^n)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.1.4.4" '(
  ("Rubi 1.1.4.4 #1" (* ?Pq (^ (+ (* ?a (^ x ?j)) (* ?b (^ x ?n))) ?p)) #t (+) 1 ())
  ("Rubi 1.1.4.4 #2" (* (^ x ?m) ?Pq (^ (+ (* ?a (^ x ?j)) (* ?b (^ x ?n))) ?p)) #t (+) 2 ())
  ("Rubi 1.1.4.4 #3" (* (^ (* ?c x) ?m) ?Pq (^ (+ (* ?a (^ x ?j)) (* ?b (^ x ?n))) ?p)) #t (+) 2 ())
  ("Rubi 1.1.4.4 #4" (* (^ (* ?c x) ?m) ?Pq (^ (+ (* ?a (^ x ?j)) (* ?b (^ x ?n))) ?p)) #t (+) 2 ())
  ("Rubi 1.1.4.4 #5" (* (^ x ?m) ?Pq (^ (+ (* ?a (^ x ?j)) (* ?b (^ x ?n))) ?p)) #t (+) 2 ())
  ("Rubi 1.1.4.4 #6" (* (^ (* ?c x) ?m) ?Pq (^ (+ (* ?a (^ x ?j)) (* ?b (^ x ?n))) ?p)) #t (+) 2 ())
  ("Rubi 1.1.4.4 #7" (* (^ x ?m) ?Pq (^ (+ (* ?a (^ x ?j)) (* ?b (^ x ?n))) ?p)) #t (+) 2 ())
  ("Rubi 1.1.4.4 #8" (* (^ (* ?c x) ?m) ?Pq (^ (+ (* ?a (^ x ?j)) (* ?b (^ x ?n))) ?p)) #t (+) 2 ())
  ("Rubi 1.1.4.4 #9" (* (^ (* ?c x) ?m) ?Pq (^ (+ (* ?a (^ x ?j)) (* ?b (^ x ?n))) ?p)) #t (+) 2 ())
  ("Rubi 1.1.4.4 #10" (* (^ (* ?c x) ?m) ?Pq (^ (+ (* ?a (^ x ?j)) (* ?b (^ x ?n))) ?p)) #t (+) 2 ())
  ("Rubi 1.1.4.4 #11" (* ?Pq (^ (+ (* ?a (^ x ?j)) (* ?b (^ x ?n))) ?p)) #t (+) 1 ())))
