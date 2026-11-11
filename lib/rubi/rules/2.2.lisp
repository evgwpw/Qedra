(module rubi)
; Rubi 4.17.3.0 — 2 Exponentials/2.2 (c+d x)^m (F^(g (e+f x)))^n (a+b (F^(g (e+f x)))^n)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "2.2" '(
  ("Rubi 2.2 #1" (/ (* (^ (+ ?c (* ?d x)) ?m) (^ (^ ?F (* ?g (+ ?e (* ?f x)))) ?n)) (+ ?a (* ?b (^ (^ ?F (* ?g (+ ?e (* ?f x)))) ?n)))) #t (+ + + +) 0 ())
  ("Rubi 2.2 #2" (* (^ (+ ?c (* ?d x)) ?m) (^ (^ ?F (* ?g (+ ?e (* ?f x)))) ?n) (^ (+ ?a (* ?b (^ (^ ?F (* ?g (+ ?e (* ?f x)))) ?n))) ?p)) #t (+ + + +) 3 ())
  ("Rubi 2.2 #3" (* (^ (+ ?c (* ?d x)) ?m) (^ (^ ?F (* ?g (+ ?e (* ?f x)))) ?n) (^ (+ ?a (* ?b (^ (^ ?F (* ?g (+ ?e (* ?f x)))) ?n))) ?p)) #t (+ + + +) 3 ())
  ("Rubi 2.2 #4" (* (^ (+ ?c (* ?d x)) ?m) (^ (* ?k (^ ?G (* ?j (+ ?h (* ?i x))))) ?q) (^ (+ ?a (* ?b (^ (^ ?F (* ?g (+ ?e (* ?f x)))) ?n))) ?p)) #t (+ + + +) 3 ())))
