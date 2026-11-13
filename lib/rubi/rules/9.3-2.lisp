(module rubi)
; Rubi 4.17.3.0 — 9 Miscellaneous/9.3 Piecewise linear functions.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "9.3-2" '(
  ("Rubi 9.3-2 #1" (^ ?u ?m.) #t () 0 ())
  ("Rubi 9.3-2 #2" (/ ?v ?u) #t () 0 ())
  ("Rubi 9.3-2 #3" (/ (^ ?v ?n) ?u) #t () 0 ())
  ("Rubi 9.3-2 #4" (/ 1 (* ?u ?v)) #t () 0 ())
  ("Rubi 9.3-2 #5" (* (^ ?u -1) (^ ?v -1/2)) #t () 2 (-1/2 -1))
  ("Rubi 9.3-2 #6" (* (^ ?u -1) (^ ?v -1/2)) #t () 2 (-1/2 -1))
  ("Rubi 9.3-2 #7" (/ (^ ?v ?n) ?u) #t () 0 ())
  ("Rubi 9.3-2 #8" (/ (^ ?v ?n) ?u) #t () 0 ())
  ("Rubi 9.3-2 #9" (* (^ ?u -1/2) (^ ?v -1/2)) #t () 2 (-1/2 -1/2))
  ("Rubi 9.3-2 #10" (* (^ ?u -1/2) (^ ?v -1/2)) #t () 2 (-1/2 -1/2))
  ("Rubi 9.3-2 #11" (* (^ ?u ?m) (^ ?v ?n)) #t () 2 ())
  ("Rubi 9.3-2 #12" (* (^ ?u ?m) (^ ?v ?n.)) #t () 2 ())
  ("Rubi 9.3-2 #13" (* (^ ?u ?m) (^ ?v ?n.)) #t () 2 ())
  ("Rubi 9.3-2 #14" (* (^ ?u ?m) (^ ?v ?n)) #t () 2 ())
  ("Rubi 9.3-2 #15" (* (^ ?u ?m) (^ ?v ?n)) #t () 2 ())
  ("Rubi 9.3-2 #16" (* (^ ?u ?m) (^ ?v ?n)) #t () 2 ())
  ("Rubi 9.3-2 #17" (* (^ ?u ?m) (^ ?v ?n)) #t () 2 ())
  ("Rubi 9.3-2 #18" (* (^ ?u ?n.) (log (+ ?a. (* ?b. x)))) #t (log) 2 ())
  ("Rubi 9.3-2 #19" (* (^ ?u ?n.) (^ (+ ?a. (* ?b. x)) ?m.) (log (+ ?a. (* ?b. x)))) #t (log) 3 ())))
