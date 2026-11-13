(module rubi)
; Rubi 4.17.3.0 — 1 Algebraic functions/1.1 Binomial products/1.1.1 Linear/1.1.1.6 P(x) (a+b x)^m (c+d x)^n (e+f x)^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "1.1.1.6" '(
  ("Rubi 1.1.1.6 #1" (* ?Px (^ (+ ?a. (* ?b. x)) ?m.) (^ (+ ?c. (* ?d. x)) ?n.) (^ (+ ?e. (* ?f. x)) ?p.)) #t () 3 ())
  ("Rubi 1.1.1.6 #2" (* ?Px (^ (+ ?a. (* ?b. x)) ?m) (^ (+ ?c. (* ?d. x)) ?n) (^ (+ ?e. (* ?f. x)) ?p.)) #t () 3 ())
  ("Rubi 1.1.1.6 #3" (* ?Px (^ (+ ?a. (* ?b. x)) ?m.) (^ (+ ?c. (* ?d. x)) ?n.) (^ (+ ?e. (* ?f. x)) ?p.)) #t () 3 ())
  ("Rubi 1.1.1.6 #4" (* ?Px (^ (+ ?a. (* ?b. x)) ?m.) (^ (+ ?c. (* ?d. x)) ?n.) (^ (+ ?e. (* ?f. x)) ?p.)) #t () 3 ())
  ("Rubi 1.1.1.6 #5" (* ?Px (^ (+ ?a. (* ?b. x)) ?m) (^ (+ ?c. (* ?d. x)) ?n.) (^ (+ ?e. (* ?f. x)) ?p.)) #t () 3 ())
  ("Rubi 1.1.1.6 #6" (* ?Px (^ (+ ?a. (* ?b. x)) ?m) (^ (+ ?c. (* ?d. x)) ?n.) (^ (+ ?e. (* ?f. x)) ?p.)) #t () 3 ())
  ("Rubi 1.1.1.6 #7" (* ?Px (^ (+ ?a. (* ?b. x)) ?m.) (^ (+ ?c. (* ?d. x)) ?n.) (^ (+ ?e. (* ?f. x)) ?p.)) #t () 3 ())))
