(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.5 u (a+b arctanh(c+d x))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "7.3.5" '(
  ("Rubi 7.3.5 #1" (^ (+ ?a (* ?b (atanh (+ ?c (* ?d x))))) ?p) #t (+ atanh +) 0 ())
  ("Rubi 7.3.5 #2" (^ (+ ?a (* ?b (acoth (+ ?c (* ?d x))))) ?p) #t (+ acoth +) 0 ())
  ("Rubi 7.3.5 #3" (^ (+ ?a (* ?b (atanh (+ ?c (* ?d x))))) ?p) #t (+ atanh +) 0 ())
  ("Rubi 7.3.5 #4" (^ (+ ?a (* ?b (acoth (+ ?c (* ?d x))))) ?p) #t (+ acoth +) 0 ())
  ("Rubi 7.3.5 #5" (* (^ (+ ?e (* ?f x)) ?m) (^ (+ ?a (* ?b (atanh (+ ?c (* ?d x))))) ?p)) #t (+ atanh + +) 2 ())
  ("Rubi 7.3.5 #6" (* (^ (+ ?e (* ?f x)) ?m) (^ (+ ?a (* ?b (acoth (+ ?c (* ?d x))))) ?p)) #t (+ acoth + +) 2 ())
  ("Rubi 7.3.5 #7" (* (^ (+ ?e (* ?f x)) ?m) (^ (+ ?a (* ?b (atanh (+ ?c (* ?d x))))) ?p)) #t (+ atanh + +) 2 ())
  ("Rubi 7.3.5 #8" (* (^ (+ ?e (* ?f x)) ?m) (^ (+ ?a (* ?b (acoth (+ ?c (* ?d x))))) ?p)) #t (+ acoth + +) 2 ())
  ("Rubi 7.3.5 #9" (* (^ (+ ?e (* ?f x)) ?m) (^ (+ ?a (* ?b (atanh (+ ?c (* ?d x))))) ?p)) #t (+ atanh + +) 2 ())
  ("Rubi 7.3.5 #10" (* (^ (+ ?e (* ?f x)) ?m) (^ (+ ?a (* ?b (acoth (+ ?c (* ?d x))))) ?p)) #t (+ acoth + +) 2 ())
  ("Rubi 7.3.5 #11" (* (^ (+ ?e (* ?f x)) ?m) (^ (+ ?a (* ?b (atanh (+ ?c (* ?d x))))) ?p)) #t (+ atanh + +) 2 ())
  ("Rubi 7.3.5 #12" (* (^ (+ ?e (* ?f x)) ?m) (^ (+ ?a (* ?b (acoth (+ ?c (* ?d x))))) ?p)) #t (+ acoth + +) 2 ())
  ("Rubi 7.3.5 #13" (/ (atanh (+ ?c (* ?d x))) (+ ?e (* ?f (^ x ?n)))) #t (+ + atanh) 0 ())
  ("Rubi 7.3.5 #14" (/ (acoth (+ ?c (* ?d x))) (+ ?e (* ?f (^ x ?n)))) #t (+ + acoth) 0 ())
  ("Rubi 7.3.5 #15" (/ (atanh (+ ?c (* ?d x))) (+ ?e (* ?f (^ x ?n)))) #t (+ + atanh) 0 ())
  ("Rubi 7.3.5 #16" (/ (acoth (+ ?c (* ?d x))) (+ ?e (* ?f (^ x ?n)))) #t (+ + acoth) 0 ())
  ("Rubi 7.3.5 #17" (* (^ (+ ?A (* ?B x) (* ?C (^ x 2))) ?q) (^ (+ ?a (* ?b (atanh (+ ?c (* ?d x))))) ?p)) #t (+ atanh + +) 2 (2))
  ("Rubi 7.3.5 #18" (* (^ (+ ?A (* ?B x) (* ?C (^ x 2))) ?q) (^ (+ ?a (* ?b (acoth (+ ?c (* ?d x))))) ?p)) #t (+ acoth + +) 2 (2))
  ("Rubi 7.3.5 #19" (* (^ (+ ?e (* ?f x)) ?m) (^ (+ ?A (* ?B x) (* ?C (^ x 2))) ?q) (^ (+ ?a (* ?b (atanh (+ ?c (* ?d x))))) ?p)) #t (+ atanh + + +) 3 (2))
  ("Rubi 7.3.5 #20" (* (^ (+ ?e (* ?f x)) ?m) (^ (+ ?A (* ?B x) (* ?C (^ x 2))) ?q) (^ (+ ?a (* ?b (acoth (+ ?c (* ?d x))))) ?p)) #t (+ acoth + + +) 3 (2))))
