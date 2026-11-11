(module rubi)
; Rubi 4.17.3.0 — 5 Inverse trig functions/5.3 Inverse tangent/5.3.3 (d+e x)^m (a+b arctan(c x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "5.3.3" '(
  ("Rubi 5.3.3 #1" (/ (^ (+ ?a (* ?b (atan (* ?c x)))) ?p) (+ ?d (* ?e x))) #t (+ atan +) 0 ())
  ("Rubi 5.3.3 #2" (/ (^ (+ ?a (* ?b (acot (* ?c x)))) ?p) (+ ?d (* ?e x))) #t (+ acot +) 0 ())
  ("Rubi 5.3.3 #3" (/ (+ ?a (* ?b (atan (* ?c x)))) (+ ?d (* ?e x))) #t (+ atan +) 0 ())
  ("Rubi 5.3.3 #4" (/ (+ ?a (* ?b (acot (* ?c x)))) (+ ?d (* ?e x))) #t (+ acot +) 0 ())
  ("Rubi 5.3.3 #5" (/ (^ (+ ?a (* ?b (atan (* ?c x)))) 2) (+ ?d (* ?e x))) #t (+ atan +) 0 (2))
  ("Rubi 5.3.3 #6" (/ (^ (+ ?a (* ?b (acot (* ?c x)))) 2) (+ ?d (* ?e x))) #t (+ acot +) 0 (2))
  ("Rubi 5.3.3 #7" (/ (^ (+ ?a (* ?b (atan (* ?c x)))) 3) (+ ?d (* ?e x))) #t (+ atan +) 0 (3))
  ("Rubi 5.3.3 #8" (/ (^ (+ ?a (* ?b (acot (* ?c x)))) 3) (+ ?d (* ?e x))) #t (+ acot +) 0 (3))
  ("Rubi 5.3.3 #9" (* (^ (+ ?d (* ?e x)) ?q) (+ ?a (* ?b (atan (* ?c x))))) #t (atan + +) 2 ())
  ("Rubi 5.3.3 #10" (* (^ (+ ?d (* ?e x)) ?q) (+ ?a (* ?b (acot (* ?c x))))) #t (acot + +) 2 ())
  ("Rubi 5.3.3 #11" (* (^ (+ ?d (* ?e x)) ?q) (^ (+ ?a (* ?b (atan (* ?c x)))) ?p)) #t (atan + +) 2 ())
  ("Rubi 5.3.3 #12" (* (^ (+ ?d (* ?e x)) ?q) (^ (+ ?a (* ?b (acot (* ?c x)))) ?p)) #t (acot + +) 2 ())
  ("Rubi 5.3.3 #13" (/ (+ ?a (* ?b (atan (* ?c (^ x ?n))))) (+ ?d (* ?e x))) #t (+ atan +) 0 ())
  ("Rubi 5.3.3 #14" (/ (+ ?a (* ?b (acot (* ?c (^ x ?n))))) (+ ?d (* ?e x))) #t (+ acot +) 0 ())
  ("Rubi 5.3.3 #15" (/ (+ ?a (* ?b (atan (* ?c (^ x ?n))))) (+ ?d (* ?e x))) #t (+ atan +) 0 ())
  ("Rubi 5.3.3 #16" (/ (+ ?a (* ?b (acot (* ?c (^ x ?n))))) (+ ?d (* ?e x))) #t (+ acot +) 0 ())
  ("Rubi 5.3.3 #17" (* (^ (+ ?d (* ?e x)) ?m) (+ ?a (* ?b (atan (* ?c (^ x ?n)))))) #t (atan + +) 2 ())
  ("Rubi 5.3.3 #18" (* (^ (+ ?d (* ?e x)) ?m) (+ ?a (* ?b (acot (* ?c (^ x ?n)))))) #t (acot + +) 2 ())
  ("Rubi 5.3.3 #19" (* (^ (+ ?d (* ?e x)) ?m) (^ (+ ?a (* ?b (atan (* ?c (^ x ?n))))) ?p)) #t (atan + +) 2 ())
  ("Rubi 5.3.3 #20" (* (^ (+ ?d (* ?e x)) ?m) (^ (+ ?a (* ?b (acot (* ?c (^ x ?n))))) ?p)) #t (acot + +) 2 ())
  ("Rubi 5.3.3 #21" (* (^ (+ ?d (* ?e x)) ?m) (^ (+ ?a (* ?b (atan (* ?c (^ x ?n))))) ?p)) #t (atan + +) 2 ())
  ("Rubi 5.3.3 #22" (* (^ (+ ?d (* ?e x)) ?m) (^ (+ ?a (* ?b (acot (* ?c (^ x ?n))))) ?p)) #t (acot + +) 2 ())))
