(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.11 (e x)^m (a+b tan(c+d x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.3.11" '(
  ("Rubi 4.3.11 #1" (^ (+ ?a. (* ?b. (tan (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (tan) 0 ())
  ("Rubi 4.3.11 #2" (^ (+ ?a. (* ?b. (cot (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (cot) 0 ())
  ("Rubi 4.3.11 #3" (^ (+ ?a. (* ?b. (tan (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (tan) 0 ())
  ("Rubi 4.3.11 #4" (^ (+ ?a. (* ?b. (cot (+ ?c. (* ?d. (^ x ?n)))))) ?p.) #t (cot) 0 ())
  ("Rubi 4.3.11 #5" (^ (+ ?a. (* ?b. (tan (+ ?c. (* ?d. (^ ?u ?n)))))) ?p.) #t (tan) 0 ())
  ("Rubi 4.3.11 #6" (^ (+ ?a. (* ?b. (cot (+ ?c. (* ?d. (^ ?u ?n)))))) ?p.) #t (cot) 0 ())
  ("Rubi 4.3.11 #7" (^ (+ ?a. (* ?b. (tan ?u))) ?p.) #t (tan) 0 ())
  ("Rubi 4.3.11 #8" (^ (+ ?a. (* ?b. (cot ?u))) ?p.) #t (cot) 0 ())
  ("Rubi 4.3.11 #9" (* (^ x ?m.) (^ (+ ?a. (* ?b. (tan (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (tan) 2 ())
  ("Rubi 4.3.11 #10" (* (^ x ?m.) (^ (+ ?a. (* ?b. (cot (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (cot) 2 ())
  ("Rubi 4.3.11 #11" (* (^ x ?m.) (^ (tan (+ ?c. (* ?d. (^ x ?n)))) 2)) #t (tan) 2 (2))
  ("Rubi 4.3.11 #12" (* (^ x ?m.) (^ (cot (+ ?c. (* ?d. (^ x ?n)))) 2)) #t (cot) 2 (2))
  ("Rubi 4.3.11 #13" (* (^ x ?m.) (^ (+ ?a. (* ?b. (tan (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (tan) 2 ())
  ("Rubi 4.3.11 #14" (* (^ x ?m.) (^ (+ ?a. (* ?b. (cot (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (cot) 2 ())
  ("Rubi 4.3.11 #15" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (tan (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (tan) 2 ())
  ("Rubi 4.3.11 #16" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (cot (+ ?c. (* ?d. (^ x ?n)))))) ?p.)) #t (cot) 2 ())
  ("Rubi 4.3.11 #17" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (tan ?u))) ?p.)) #t (tan) 2 ())
  ("Rubi 4.3.11 #18" (* (^ (* ?e x) ?m.) (^ (+ ?a. (* ?b. (cot ?u))) ?p.)) #t (cot) 2 ())
  ("Rubi 4.3.11 #19" (* (^ x ?m.) (^ (sec (+ ?a. (* ?b. (^ x ?n.)))) ?p.) (^ (tan (+ ?a. (* ?b. (^ x ?n.)))) ?q.)) #t (tan sec) 3 ())
  ("Rubi 4.3.11 #20" (* (^ x ?m.) (^ (csc (+ ?a. (* ?b. (^ x ?n.)))) ?p.) (^ (cot (+ ?a. (* ?b. (^ x ?n.)))) ?q.)) #t (cot csc) 3 ())))
