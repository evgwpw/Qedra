(module rubi)
; Rubi 4.17.3.0 — 6 Hyperbolic functions/6.5 Hyperbolic secant/6.5.11 (e x)^m (a+b sech(c+d x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "6.5.11" '(
  ("Rubi 6.5.11 #1" (^ (+ ?a. (* ?b. (sech (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (sech) 0 ())
  ("Rubi 6.5.11 #2" (^ (+ ?a. (* ?b. (csch (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (csch) 0 ())
  ("Rubi 6.5.11 #3" (^ (+ ?a. (* ?b. (sech (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (sech) 0 ())
  ("Rubi 6.5.11 #4" (^ (+ ?a. (* ?b. (csch (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (csch) 0 ())
  ("Rubi 6.5.11 #5" (^ (+ ?a. (* ?b. (sech (+ ?c. (* ?d. (^ ?u ?n)))))) ?p.) #t (sech) 0 ())
  ("Rubi 6.5.11 #6" (^ (+ ?a. (* ?b. (csch (+ ?c. (* ?d. (^ ?u ?n)))))) ?p.) #t (csch) 0 ())
  ("Rubi 6.5.11 #7" (^ (+ ?a. (* ?b. (sech ?u))) ?p.) #t (sech) 0 ())
  ("Rubi 6.5.11 #8" (^ (+ ?a. (* ?b. (csch ?u))) ?p.) #t (csch) 0 ())
  ("Rubi 6.5.11 #9" (* (^ x ?m.) (^ (+ ?a. (* ?b. (sech (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (sech) 2 ())
  ("Rubi 6.5.11 #10" (* (^ x ?m.) (^ (+ ?a. (* ?b. (csch (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (csch) 2 ())
  ("Rubi 6.5.11 #11" (* (^ x ?m.) (^ (+ ?a. (* ?b. (sech (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (sech) 2 ())
  ("Rubi 6.5.11 #12" (* (^ x ?m.) (^ (+ ?a. (* ?b. (csch (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (csch) 2 ())
  ("Rubi 6.5.11 #13" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (sech (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (sech) 2 ())
  ("Rubi 6.5.11 #14" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (csch (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (csch) 2 ())
  ("Rubi 6.5.11 #15" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (sech ?u))) ?p.)) #t (sech) 2 ())
  ("Rubi 6.5.11 #16" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (csch ?u))) ?p.)) #t (csch) 2 ())
  ("Rubi 6.5.11 #17" (* (^ x ?m.) (^ (sech (+ ?a. (* ?b. (^ x ?n.)))) ?p) (sinh (+ ?a. (* ?b. (^ x ?n.))))) #t (sinh sech) 3 ())
  ("Rubi 6.5.11 #18" (* (^ x ?m.) (^ (csch (+ ?a. (* ?b. (^ x ?n.)))) ?p) (cosh (+ ?a. (* ?b. (^ x ?n.))))) #t (cosh csch) 3 ())))
