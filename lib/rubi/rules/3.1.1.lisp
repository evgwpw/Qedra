(module rubi)
; Rubi 4.17.3.0 — 3 Logarithms/3.1.1 (a+b log(c x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "3.1.1" '(
  ("Rubi 3.1.1 #1" (log (* ?c (^ x ?n))) #t (log) 0 ())
  ("Rubi 3.1.1 #2" (^ (+ ?a (* ?b (log (* ?c (^ x ?n))))) ?p) #t (log +) 0 ())
  ("Rubi 3.1.1 #3" (^ (+ ?a (* ?b (log (* ?c (^ x ?n))))) ?p) #t (log +) 0 ())
  ("Rubi 3.1.1 #4" (/ 1 (log (* ?c x))) #t (log) 0 ())
  ("Rubi 3.1.1 #5" (^ (+ ?a (* ?b (log (* ?c (^ x ?n))))) ?p) #t (log +) 0 ())
  ("Rubi 3.1.1 #6" (^ (+ ?a (* ?b (log (* ?c (^ x ?n))))) ?p) #t (log +) 0 ())))
