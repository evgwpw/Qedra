(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.0.3 (a csc)^m (b sec)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.1.0.3" '(
  ("Rubi 4.1.0.3 #1" (* (^ (* ?a (csc (+ ?e (* ?f x)))) ?m) (^ (* ?b (sec (+ ?e (* ?f x)))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #2" (* (^ (csc (+ ?e (* ?f x))) ?m) (^ (sec (+ ?e (* ?f x))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #3" (* (^ (* ?a (csc (+ ?e (* ?f x)))) ?m) (^ (sec (+ ?e (* ?f x))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #4" (* (^ (* ?a (sec (+ ?e (* ?f x)))) ?m) (^ (csc (+ ?e (* ?f x))) ?n)) #t (+ csc + sec) 2 ())
  ("Rubi 4.1.0.3 #5" (* (^ (* ?a (csc (+ ?e (* ?f x)))) ?m) (^ (* ?b (sec (+ ?e (* ?f x)))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #6" (* (^ (* ?a (csc (+ ?e (* ?f x)))) ?m) (^ (* ?b (sec (+ ?e (* ?f x)))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #7" (* (^ (* ?a (csc (+ ?e (* ?f x)))) ?m) (^ (* ?b (sec (+ ?e (* ?f x)))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #8" (* (^ (* ?a (csc (+ ?e (* ?f x)))) ?m) (^ (* ?b (sec (+ ?e (* ?f x)))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #9" (* (^ (* ?a (csc (+ ?e (* ?f x)))) ?m) (^ (* ?b (sec (+ ?e (* ?f x)))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #10" (* (^ (* ?a (csc (+ ?e (* ?f x)))) ?m) (^ (* ?b (sec (+ ?e (* ?f x)))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #11" (* (^ (* ?a (csc (+ ?e (* ?f x)))) ?m) (^ (* ?b (sec (+ ?e (* ?f x)))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #12" (* (^ (* ?a (csc (+ ?e (* ?f x)))) ?m) (^ (* ?b (sec (+ ?e (* ?f x)))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #13" (* (^ (* ?a (csc (+ ?e (* ?f x)))) ?m) (^ (* ?b (sec (+ ?e (* ?f x)))) ?n)) #t (+ sec + csc) 2 ())
  ("Rubi 4.1.0.3 #14" (* (^ (* ?a (sec (+ ?e (* ?f x)))) ?m) (^ (* ?b (csc (+ ?e (* ?f x)))) ?n)) #t (+ csc + sec) 2 ())))
