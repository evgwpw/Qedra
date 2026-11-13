(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.2 Trinomial products/1.2.4 Improper/1.2.4.3 (d+e x^(n-q)) (a x^q+b x^n+c x^(2 n-q))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.2.4.3" '(
  ("Rubi 1.2.4.3 #1" (* (+ ?A (* ?B (^ x ?r))) (^ (+ (* ?a (^ x ?q)) (* ?b (^ x ?n)) (* ?c (^ x ?j))) ?p)) #t (+ +) 2 ())
  ("Rubi 1.2.4.3 #2" (* (+ ?A (* ?B (^ x ?j))) (^ (+ (* ?a (^ x ?q)) (* ?b (^ x ?n)) (* ?c (^ x ?r))) -1/2)) #t (+ +) 2 (-1/2))
  ("Rubi 1.2.4.3 #3" (* (+ ?A (* ?B (^ x ?r))) (^ (+ (* ?a (^ x ?q)) (* ?b (^ x ?n)) (* ?c (^ x ?j))) ?p)) #t (+ +) 2 ())
  ("Rubi 1.2.4.3 #4" (* (+ ?A (* ?B (^ x ?r))) (^ (+ (* ?a (^ x ?q)) (* ?c (^ x ?j))) ?p)) #t (+ +) 2 ())
  ("Rubi 1.2.4.3 #5" (* (+ ?A (* ?B (^ x ?r))) (^ (+ (* ?a (^ x ?q)) (* ?b (^ x ?n)) (* ?c (^ x ?j))) ?p)) #t (+ +) 2 ())
  ("Rubi 1.2.4.3 #6" (* (+ ?A (* ?B (^ x ?r))) (^ (+ (* ?a (^ x ?q)) (* ?c (^ x ?j))) ?p)) #t (+ +) 2 ())
  ("Rubi 1.2.4.3 #7" (* (+ ?A (* ?B (^ x ?j))) (^ (+ (* ?a (^ x ?q)) (* ?b (^ x ?n)) (* ?c (^ x ?r))) ?p)) #t (+ +) 2 ())
  ("Rubi 1.2.4.3 #8" (* (+ ?A (* ?B (^ ?u ?j))) (^ (+ (* ?a (^ ?u ?q)) (* ?b (^ ?u ?n)) (* ?c (^ ?u ?r))) ?p)) #t (+ +) 2 ())))
