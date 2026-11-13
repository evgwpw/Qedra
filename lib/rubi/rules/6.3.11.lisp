(module rubi)
; Rubi 4.17.3.0 — 6 Hyperbolic functions/6.3 Hyperbolic tangent/6.3.11 (e x)^m (a+b tanh(c+d x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "6.3.11" '(
  ("Rubi 6.3.11 #1" (^ (+ ?a. (* ?b. (tanh (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (tanh) 0 ())
  ("Rubi 6.3.11 #2" (^ (+ ?a. (* ?b. (coth (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (coth) 0 ())
  ("Rubi 6.3.11 #3" (^ (+ ?a. (* ?b. (tanh (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (tanh) 0 ())
  ("Rubi 6.3.11 #4" (^ (+ ?a. (* ?b. (coth (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (coth) 0 ())
  ("Rubi 6.3.11 #5" (^ (+ ?a. (* ?b. (tanh (+ ?c. (* ?d. (^ ?u ?n)))))) ?p.) #t (tanh) 0 ())
  ("Rubi 6.3.11 #6" (^ (+ ?a. (* ?b. (coth (+ ?c. (* ?d. (^ ?u ?n)))))) ?p.) #t (coth) 0 ())
  ("Rubi 6.3.11 #7" (^ (+ ?a. (* ?b. (tanh ?u))) ?p.) #t (tanh) 0 ())
  ("Rubi 6.3.11 #8" (^ (+ ?a. (* ?b. (coth ?u))) ?p.) #t (coth) 0 ())
  ("Rubi 6.3.11 #9" (* (^ x ?m.) (^ (+ ?a. (* ?b. (tanh (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (tanh) 2 ())
  ("Rubi 6.3.11 #10" (* (^ x ?m.) (^ (+ ?a. (* ?b. (coth (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (coth) 2 ())
  ("Rubi 6.3.11 #11" (* (^ x ?m.) (^ (tanh (+ ?c. (* ?d. (^ x ?n)))) 2)) #t (tanh) 2 (2))
  ("Rubi 6.3.11 #12" (* (^ x ?m.) (^ (coth (+ ?c. (* ?d. (^ x ?n)))) 2)) #t (coth) 2 (2))
  ("Rubi 6.3.11 #13" (* (^ x ?m.) (^ (+ ?a. (* ?b. (tanh (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (tanh) 2 ())
  ("Rubi 6.3.11 #14" (* (^ x ?m.) (^ (+ ?a. (* ?b. (coth (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (coth) 2 ())
  ("Rubi 6.3.11 #15" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (tanh (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (tanh) 2 ())
  ("Rubi 6.3.11 #16" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (coth (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (coth) 2 ())
  ("Rubi 6.3.11 #17" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (tanh ?u))) ?p.)) #t (tanh) 2 ())
  ("Rubi 6.3.11 #18" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (coth ?u))) ?p.)) #t (coth) 2 ())
  ("Rubi 6.3.11 #19" (* (^ x ?m.) (^ (sech (+ ?a. (* ?b. (^ x ?n.)))) ?p.) (^ (tanh (+ ?a. (* ?b. (^ x ?n.)))) ?q.)) #t (tanh sech) 3 ())
  ("Rubi 6.3.11 #20" (* (^ x ?m.) (^ (csch (+ ?a. (* ?b. (^ x ?n.)))) ?p.) (^ (coth (+ ?a. (* ?b. (^ x ?n.)))) ?q.)) #t (coth csch) 3 ())))
