(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.5 Secant/4.5.1.1 (a+b sec)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.5.1.1" '(
  ("Rubi 4.5.1.1 #1" (^ (csc (+ ?c. (* ?d. x))) ?n) #t (csc) 0 ())
  ("Rubi 4.5.1.1 #2" (^ (* ?b. (csc (+ ?c. (* ?d. x)))) ?n) #t (csc) 0 ())
  ("Rubi 4.5.1.1 #3" (^ (* ?b. (csc (+ ?c. (* ?d. x)))) ?n) #t (csc) 0 ())
  ("Rubi 4.5.1.1 #4" (csc (+ ?c. (* ?d. x))) #t (csc) 0 ())
  ("Rubi 4.5.1.1 #5" (^ (* ?b. (csc (+ ?c. (* ?d. x)))) ?n) #t (csc) 0 ())
  ("Rubi 4.5.1.1 #6" (^ (* ?b. (csc (+ ?c. (* ?d. x)))) ?n) #t (csc) 0 ())
  ("Rubi 4.5.1.1 #7" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) 2) #t (csc +) 0 (2))
  ("Rubi 4.5.1.1 #8" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) 1/2) #t (csc +) 0 (1/2))
  ("Rubi 4.5.1.1 #9" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) ?n) #t (csc +) 0 ())
  ("Rubi 4.5.1.1 #10" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) -1/2) #t (csc +) 0 (-1/2))
  ("Rubi 4.5.1.1 #11" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) ?n) #t (csc +) 0 ())
  ("Rubi 4.5.1.1 #12" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) ?n) #t (csc +) 0 ())
  ("Rubi 4.5.1.1 #13" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) ?n) #t (csc +) 0 ())
  ("Rubi 4.5.1.1 #14" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) 1/2) #t (csc +) 0 (1/2))
  ("Rubi 4.5.1.1 #15" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) (/ 3 2)) #t (csc +) 0 ())
  ("Rubi 4.5.1.1 #16" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) ?n) #t (csc +) 0 ())
  ("Rubi 4.5.1.1 #17" (/ 1 (+ ?a (* ?b. (csc (+ ?c. (* ?d. x)))))) #t (csc +) 0 ())
  ("Rubi 4.5.1.1 #18" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) -1/2) #t (csc +) 0 (-1/2))
  ("Rubi 4.5.1.1 #19" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) ?n) #t (csc +) 0 ())
  ("Rubi 4.5.1.1 #20" (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) ?n) #t (csc +) 0 ())))
