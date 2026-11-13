(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.1.1 (a+b tan)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.3.1.1" '(
  ("Rubi 4.3.1.1 #1" (^ (* ?b. (tan (+ ?c. (* ?d. x)))) ?n) #t (tan) 0 ())
  ("Rubi 4.3.1.1 #2" (^ (* ?b. (tan (+ ?c. (* ?d. x)))) ?n) #t (tan) 0 ())
  ("Rubi 4.3.1.1 #3" (tan (+ ?c. (* ?d. x))) #t (tan) 0 ())
  ("Rubi 4.3.1.1 #4" (^ (* ?b. (tan (+ ?c. (* ?d. x)))) ?n) #t (tan) 0 ())
  ("Rubi 4.3.1.1 #5" (^ (+ ?a (* ?b. (tan (+ ?c. (* ?d. x))))) 2) #t (tan +) 0 (2))
  ("Rubi 4.3.1.1 #6" (^ (+ ?a (* ?b. (tan (+ ?c. (* ?d. x))))) ?n) #t (tan +) 0 ())
  ("Rubi 4.3.1.1 #7" (^ (+ ?a (* ?b. (tan (+ ?c. (* ?d. x))))) ?n) #t (tan +) 0 ())
  ("Rubi 4.3.1.1 #8" (^ (+ ?a (* ?b. (tan (+ ?c. (* ?d. x))))) 1/2) #t (tan +) 0 (1/2))
  ("Rubi 4.3.1.1 #9" (^ (+ ?a (* ?b. (tan (+ ?c. (* ?d. x))))) ?n) #t (tan +) 0 ())
  ("Rubi 4.3.1.1 #10" (^ (+ ?a (* ?b. (tan (+ ?c. (* ?d. x))))) ?n) #t (tan +) 0 ())
  ("Rubi 4.3.1.1 #11" (^ (+ ?a (* ?b. (tan (+ ?c. (* ?d. x))))) ?n) #t (tan +) 0 ())
  ("Rubi 4.3.1.1 #12" (/ 1 (+ ?a (* ?b. (tan (+ ?c. (* ?d. x)))))) #t (tan +) 0 ())
  ("Rubi 4.3.1.1 #13" (^ (+ ?a (* ?b. (tan (+ ?c. (* ?d. x))))) ?n) #t (tan +) 0 ())))
