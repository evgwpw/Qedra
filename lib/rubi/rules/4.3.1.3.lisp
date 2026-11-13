(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.1.3 (d sin)^m (a+b tan)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.3.1.3" '(
  ("Rubi 4.3.1.3 #1" (* (^ (sin (+ ?e (* ?f x))) ?m) (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?n)) #t (+ tan + + sin) 2 ())
  ("Rubi 4.3.1.3 #2" (* (^ (sin (+ ?e (* ?f x))) ?m) (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?n)) #t (+ tan + + sin) 2 ())
  ("Rubi 4.3.1.3 #3" (* (^ (sin (+ ?e (* ?f x))) ?m) (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?n)) #t (+ tan + + sin) 2 ())
  ("Rubi 4.3.1.3 #4" (* (^ (* ?d (csc (+ ?e (* ?f x)))) ?m) (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?n)) #t (+ tan + + csc) 2 ())
  ("Rubi 4.3.1.3 #5" (* (^ (cos (+ ?e (* ?f x))) ?m) (^ (sin (+ ?e (* ?f x))) ?p) (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?n)) #t (+ tan + + sin + cos) 3 ())
  ("Rubi 4.3.1.3 #6" (* (^ (sin (+ ?e (* ?f x))) ?m) (^ (cos (+ ?e (* ?f x))) ?p) (^ (+ ?a (* ?b (cot (+ ?e (* ?f x))))) ?n)) #t (+ cot + + cos + sin) 3 ())))
