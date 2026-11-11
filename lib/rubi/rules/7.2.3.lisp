(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.2 Inverse hyperbolic cosine/7.2.3 (d+e x^2)^p (a+b arccosh(c x))^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "7.2.3" '(
  ("Rubi 7.2.3 #1" (* (^ (+ ?d1 (* ?e1 x)) ?p) (^ (+ ?d2 (* ?e2 x)) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + + +) 3 ())
  ("Rubi 7.2.3 #2" (* (^ (+ ?d (* ?e (^ x 2))) -1/2) (^ (+ ?a (* ?b (acosh (* ?c x)))) -1)) #t (acosh + +) 2 (-1 2 -1/2))
  ("Rubi 7.2.3 #3" (* (^ (+ ?d1 (* ?e1 x)) -1/2) (^ (+ ?d2 (* ?e2 x)) -1/2) (^ (+ ?a (* ?b (acosh (* ?c x)))) -1)) #t (acosh + + +) 3 (-1 -1/2 -1/2))
  ("Rubi 7.2.3 #4" (* (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n) (^ (+ ?d (* ?e (^ x 2))) -1/2)) #t (+ acosh +) 2 (2 -1/2))
  ("Rubi 7.2.3 #5" (* (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n) (* (^ (+ ?d1 (* ?e1 x)) -1/2) (^ (+ ?d2 (* ?e2 x)) -1/2))) #t (+ + acosh +) 2 (-1/2 -1/2))
  ("Rubi 7.2.3 #6" (* (^ (+ ?d (* ?e (^ x 2))) ?p) (+ ?a (* ?b (acosh (* ?c x))))) #t (acosh + +) 2 (2))
  ("Rubi 7.2.3 #7" (* (^ (+ ?d (* ?e (^ x 2))) 1/2) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + +) 2 (2 1/2))
  ("Rubi 7.2.3 #8" (* (^ (+ ?d1 (* ?e1 x)) 1/2) (^ (+ ?d2 (* ?e2 x)) 1/2) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + + +) 3 (1/2 1/2))
  ("Rubi 7.2.3 #9" (* (^ (+ ?d (* ?e (^ x 2))) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + +) 2 (2))
  ("Rubi 7.2.3 #10" (* (^ (+ ?d1 (* ?e1 x)) ?p) (^ (+ ?d2 (* ?e2 x)) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + + +) 3 ())
  ("Rubi 7.2.3 #11" (/ (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n) (^ (+ ?d (* ?e (^ x 2))) (/ 3 2))) #t (+ acosh +) 0 (2))
  ("Rubi 7.2.3 #12" (/ (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n) (* (^ (+ ?d1 (* ?e1 x)) (/ 3 2)) (^ (+ ?d2 (* ?e2 x)) (/ 3 2)))) #t (+ + acosh +) 0 ())
  ("Rubi 7.2.3 #13" (* (^ (+ ?d (* ?e (^ x 2))) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + +) 2 (2))
  ("Rubi 7.2.3 #14" (* (^ (+ ?d1 (* ?e1 x)) ?p) (^ (+ ?d2 (* ?e2 x)) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + + +) 3 ())
  ("Rubi 7.2.3 #15" (/ (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n) (+ ?d (* ?e (^ x 2)))) #t (+ acosh +) 0 (2))
  ("Rubi 7.2.3 #16" (* (^ (+ ?d (* ?e (^ x 2))) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + +) 2 (2))
  ("Rubi 7.2.3 #17" (* (^ (+ ?d1 (* ?e1 x)) ?p) (^ (+ ?d2 (* ?e2 x)) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + + +) 3 ())
  ("Rubi 7.2.3 #18" (* (^ (+ ?d (* ?e (^ x 2))) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + +) 2 (2))
  ("Rubi 7.2.3 #19" (* (^ (+ ?d1 (* ?e1 x)) ?p) (^ (+ ?d2 (* ?e2 x)) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + + +) 3 ())
  ("Rubi 7.2.3 #20" (* (^ (+ ?d (* ?e (^ x 2))) ?p) (+ ?a (* ?b (acosh (* ?c x))))) #t (acosh + +) 2 (2))
  ("Rubi 7.2.3 #21" (* (^ (+ ?d (* ?e (^ x 2))) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + +) 2 (2))
  ("Rubi 7.2.3 #22" (* (^ (+ ?d (* ?e (^ x 2))) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + +) 2 (2))
  ("Rubi 7.2.3 #23" (* (^ (+ ?d1 (* ?e1 x)) ?p) (^ (+ ?d2 (* ?e2 x)) ?p) (^ (+ ?a (* ?b (acosh (* ?c x)))) ?n)) #t (acosh + + +) 3 ())))
