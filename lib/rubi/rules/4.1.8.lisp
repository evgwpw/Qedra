(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.8 trig^m (a+b cos^p+c sin^q)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.1.8" '(
  ("Rubi 4.1.8 #1" (* (^ (sin (+ ?d (* ?e x))) ?m) (^ (+ ?a (* ?b (^ (cos (+ ?d (* ?e x))) ?p)) (* ?c (^ (sin (+ ?d (* ?e x))) ?q))) ?n)) #t (+ sin + cos + + sin) 2 ())
  ("Rubi 4.1.8 #2" (* (^ (cos (+ ?d (* ?e x))) ?m) (^ (+ ?a (* ?b (^ (sin (+ ?d (* ?e x))) ?p)) (* ?c (^ (cos (+ ?d (* ?e x))) ?q))) ?n)) #t (+ cos + sin + + cos) 2 ())
  ("Rubi 4.1.8 #3" (* (^ (sin (+ ?d (* ?e x))) ?m) (^ (+ ?a (* ?b (^ (cos (+ ?d (* ?e x))) ?p)) (* ?c (^ (sin (+ ?d (* ?e x))) ?q))) ?n)) #t (+ sin + cos + + sin) 2 ())
  ("Rubi 4.1.8 #4" (* (^ (cos (+ ?d (* ?e x))) ?m) (^ (+ ?a (* ?b (^ (sin (+ ?d (* ?e x))) ?p)) (* ?c (^ (cos (+ ?d (* ?e x))) ?q))) ?n)) #t (+ cos + sin + + cos) 2 ())
  ("Rubi 4.1.8 #5" (* (^ (sin (+ ?d (* ?e x))) ?m) (^ (+ ?a (* ?b (^ (cos (+ ?d (* ?e x))) ?p)) (* ?c (^ (sin (+ ?d (* ?e x))) ?q))) ?n)) #t (+ sin + cos + + sin) 2 ())
  ("Rubi 4.1.8 #6" (* (^ (cos (+ ?d (* ?e x))) ?m) (^ (+ ?a (* ?b (^ (sin (+ ?d (* ?e x))) ?p)) (* ?c (^ (cos (+ ?d (* ?e x))) ?q))) ?n)) #t (+ cos + sin + + cos) 2 ())
  ("Rubi 4.1.8 #7" (* (^ (sin (+ ?d (* ?e x))) ?m) (^ (+ ?a (* ?b (^ (cos (+ ?d (* ?e x))) ?p)) (* ?c (^ (sin (+ ?d (* ?e x))) ?q))) ?n)) #t (+ sin + cos + + sin) 2 ())
  ("Rubi 4.1.8 #8" (* (^ (cos (+ ?d (* ?e x))) ?m) (^ (+ ?a (* ?b (^ (sin (+ ?d (* ?e x))) ?p)) (* ?c (^ (cos (+ ?d (* ?e x))) ?q))) ?n)) #t (+ cos + sin + + cos) 2 ())))
