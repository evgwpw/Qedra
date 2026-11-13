(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.5 Secant/4.5.11 (e x)^m (a+b sec(c+d x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.5.11" '(
  ("Rubi 4.5.11 #1" (^ (+ ?a. (* ?b. (sec (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (sec) 0 ())
  ("Rubi 4.5.11 #2" (^ (+ ?a. (* ?b. (csc (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (csc) 0 ())
  ("Rubi 4.5.11 #3" (^ (+ ?a. (* ?b. (sec (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (sec) 0 ())
  ("Rubi 4.5.11 #4" (^ (+ ?a. (* ?b. (csc (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (csc) 0 ())
  ("Rubi 4.5.11 #5" (^ (+ ?a. (* ?b. (sec (+ ?c. (* ?d. (^ ?u ?n)))))) ?p.) #t (sec) 0 ())
  ("Rubi 4.5.11 #6" (^ (+ ?a. (* ?b. (csc (+ ?c. (* ?d. (^ ?u ?n)))))) ?p.) #t (csc) 0 ())
  ("Rubi 4.5.11 #7" (^ (+ ?a. (* ?b. (sec ?u))) ?p.) #t (sec) 0 ())
  ("Rubi 4.5.11 #8" (^ (+ ?a. (* ?b. (csc ?u))) ?p.) #t (csc) 0 ())
  ("Rubi 4.5.11 #9" (* (^ x ?m.) (^ (+ ?a. (* ?b. (sec (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (sec) 2 ())
  ("Rubi 4.5.11 #10" (* (^ x ?m.) (^ (+ ?a. (* ?b. (csc (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (csc) 2 ())
  ("Rubi 4.5.11 #11" (* (^ x ?m.) (^ (+ ?a. (* ?b. (sec (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (sec) 2 ())
  ("Rubi 4.5.11 #12" (* (^ x ?m.) (^ (+ ?a. (* ?b. (csc (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (csc) 2 ())
  ("Rubi 4.5.11 #13" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (sec (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (sec) 2 ())
  ("Rubi 4.5.11 #14" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (csc (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (csc) 2 ())
  ("Rubi 4.5.11 #15" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (sec ?u))) ?p.)) #t (sec) 2 ())
  ("Rubi 4.5.11 #16" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (csc ?u))) ?p.)) #t (csc) 2 ())
  ("Rubi 4.5.11 #17" (* (^ x ?m.) (^ (sec (+ ?a. (* ?b. (^ x ?n.)))) ?p) (sin (+ ?a. (* ?b. (^ x ?n.))))) #t (sin sec) 3 ())
  ("Rubi 4.5.11 #18" (* (^ x ?m.) (^ (csc (+ ?a. (* ?b. (^ x ?n.)))) ?p) (cos (+ ?a. (* ?b. (^ x ?n.))))) #t (cos csc) 3 ())))
