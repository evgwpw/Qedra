(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.5 Secant/4.5.1.3 (d sin)^n (a+b sec)^m.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.5.1.3" '(
  ("Rubi 4.5.1.3 #1" (* (^ (* ?g (cos (+ ?e (* ?f x)))) ?p) (^ (+ ?a (* ?b (csc (+ ?e (* ?f x))))) ?m)) #t (+ csc + + cos) 2 ())
  ("Rubi 4.5.1.3 #2" (* (^ (cos (+ ?e (* ?f x))) ?p) (^ (+ ?a (* ?b (csc (+ ?e (* ?f x))))) ?m)) #t (+ csc + + cos) 2 ())
  ("Rubi 4.5.1.3 #3" (* (^ (cos (+ ?e (* ?f x))) ?p) (^ (+ ?a (* ?b (csc (+ ?e (* ?f x))))) ?m)) #t (+ csc + + cos) 2 ())
  ("Rubi 4.5.1.3 #4" (/ (^ (+ ?a (* ?b (csc (+ ?e (* ?f x))))) ?m) (^ (cos (+ ?e (* ?f x))) 2)) #t (+ cos + csc +) 0 (2))
  ("Rubi 4.5.1.3 #5" (* (^ (* ?g (cos (+ ?e (* ?f x)))) ?p) (^ (+ ?a (* ?b (csc (+ ?e (* ?f x))))) ?m)) #t (+ csc + + cos) 2 ())
  ("Rubi 4.5.1.3 #6" (* (^ (* ?g (cos (+ ?e (* ?f x)))) ?p) (^ (+ ?a (* ?b (csc (+ ?e (* ?f x))))) ?m)) #t (+ csc + + cos) 2 ())
  ("Rubi 4.5.1.3 #7" (* (^ (* ?g (sec (+ ?e (* ?f x)))) ?p) (^ (+ ?a (* ?b (csc (+ ?e (* ?f x))))) ?m)) #t (+ csc + + sec) 2 ())))
