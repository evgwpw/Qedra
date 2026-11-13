(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.6 Miscellaneous inverse hyperbolic sine.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "7.1.6" '(
  ("Rubi 7.1.6 #1" (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. x))))) ?n.) #t (+ asinh) 0 ())
  ("Rubi 7.1.6 #2" (* (^ (+ ?e. (* ?f. x)) ?m.) (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. x))))) ?n.)) #t (+ asinh) 2 ())
  ("Rubi 7.1.6 #3" (* (^ (+ ?A. (* ?B. x) (* ?C. (^ x 2))) ?p.) (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. x))))) ?n.)) #t (+ asinh +) 2 (2))
  ("Rubi 7.1.6 #4" (* (^ (+ ?e. (* ?f. x)) ?m.) (^ (+ ?A. (* ?B. x) (* ?C. (^ x 2))) ?p.) (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. x))))) ?n.)) #t (+ asinh +) 3 (2))
  ("Rubi 7.1.6 #5" (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. (^ x 2)))))) 1/2) #t (+ asinh) 0 (2 1/2))
  ("Rubi 7.1.6 #6" (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. (^ x 2)))))) ?n) #t (+ asinh) 0 (2))
  ("Rubi 7.1.6 #7" (/ 1 (+ ?a. (* ?b. (asinh (+ ?c (* ?d. (^ x 2))))))) #t (+ asinh) 0 (2))
  ("Rubi 7.1.6 #8" (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. (^ x 2)))))) -1/2) #t (+ asinh) 0 (2 -1/2))
  ("Rubi 7.1.6 #9" (/ 1 (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. (^ x 2)))))) (/ 3 2))) #t (+ asinh) 0 (2))
  ("Rubi 7.1.6 #10" (/ 1 (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. (^ x 2)))))) 2)) #t (+ asinh) 0 (2 2))
  ("Rubi 7.1.6 #11" (^ (+ ?a. (* ?b. (asinh (+ ?c (* ?d. (^ x 2)))))) ?n) #t (+ asinh) 0 (2))
  ("Rubi 7.1.6 #12" (/ (^ (asinh (* ?a. (^ x ?p))) ?n.) x) #t (asinh) 0 ())
  ("Rubi 7.1.6 #13" (* ?u. (^ (asinh (/ ?c. (+ ?a. (* ?b. (^ x ?n.))))) ?m.)) #t (asinh) 1 ())
  ("Rubi 7.1.6 #14" (* (^ (asinh (^ (+ -1 (* ?b. (^ x 2))) 1/2)) ?n.) (^ (+ -1 (* ?b. (^ x 2))) -1/2)) #t (+ + asinh) 2 (2 -1/2 2 1/2))
  ("Rubi 7.1.6 #15" (^ ?f (* ?c. (^ (asinh (+ ?a. (* ?b. x))) ?n.))) #t (asinh) 0 ())
  ("Rubi 7.1.6 #16" (* (^ x ?m.) (^ ?f (* ?c. (^ (asinh (+ ?a. (* ?b. x))) ?n.)))) #t (asinh) 2 ())
  ("Rubi 7.1.6 #17" (asinh ?u) #t (asinh) 0 ())
  ("Rubi 7.1.6 #18" (* (^ (+ ?c. (* ?d. x)) ?m.) (+ ?a. (* ?b. (asinh ?u)))) #t (asinh) 2 ())
  ("Rubi 7.1.6 #19" (* ?v (+ ?a. (* ?b. (asinh ?u)))) #t (asinh) 1 ())
  ("Rubi 7.1.6 #20" (^ E (* ?n. (asinh ?u))) #t (asinh) 0 ())
  ("Rubi 7.1.6 #21" (* (^ x ?m.) (^ E (* ?n. (asinh ?u)))) #t (asinh) 2 ())))
