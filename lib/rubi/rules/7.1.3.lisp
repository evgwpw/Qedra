(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.1 Inverse hyperbolic sine/7.1.3 (d+e x^2)^p (a+b arcsinh(c x))^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "7.1.3" '(
  ("Rubi 7.1.3 #1" (* (^ (+ ?d (* ?e. (^ x 2))) -1/2) (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) -1)) #t (asinh +) 2 (-1 2 -1/2))
  ("Rubi 7.1.3 #2" (* (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.) (^ (+ ?d (* ?e. (^ x 2))) -1/2)) #t (+ asinh) 2 (2 -1/2))
  ("Rubi 7.1.3 #3" (* (^ (+ ?d (* ?e. (^ x 2))) ?p.) (+ ?a. (* ?b. (asinh (* ?c. x))))) #t (asinh +) 2 (2))
  ("Rubi 7.1.3 #4" (* (^ (+ ?d (* ?e. (^ x 2))) 1/2) (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.)) #t (asinh +) 2 (2 1/2))
  ("Rubi 7.1.3 #5" (* (^ (+ ?d (* ?e. (^ x 2))) ?p.) (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.)) #t (asinh +) 2 (2))
  ("Rubi 7.1.3 #6" (/ (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.) (^ (+ ?d (* ?e. (^ x 2))) (/ 3 2))) #t (+ asinh) 0 (2))
  ("Rubi 7.1.3 #7" (* (^ (+ ?d (* ?e. (^ x 2))) ?p) (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.)) #t (asinh +) 2 (2))
  ("Rubi 7.1.3 #8" (/ (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.) (+ ?d (* ?e. (^ x 2)))) #t (+ asinh) 0 (2))
  ("Rubi 7.1.3 #9" (* (^ (+ ?d (* ?e. (^ x 2))) ?p.) (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n)) #t (asinh +) 2 (2))
  ("Rubi 7.1.3 #10" (* (^ (+ ?d (* ?e. (^ x 2))) ?p.) (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.)) #t (asinh +) 2 (2))
  ("Rubi 7.1.3 #11" (* (^ (+ ?d (* ?e. (^ x 2))) ?p.) (+ ?a. (* ?b. (asinh (* ?c. x))))) #t (asinh +) 2 (2))
  ("Rubi 7.1.3 #12" (* (^ (+ ?d (* ?e. (^ x 2))) ?p.) (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.)) #t (asinh +) 2 (2))
  ("Rubi 7.1.3 #13" (* (^ (+ ?d (* ?e. (^ x 2))) ?p.) (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.)) #t (asinh +) 2 (2))
  ("Rubi 7.1.3 #14" (* (^ (+ ?d (* ?e. x)) ?p) (^ (+ ?f (* ?g. x)) ?q) (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.)) #t (asinh + +) 3 ())
  ("Rubi 7.1.3 #15" (* (^ (+ ?d (* ?e. x)) ?p) (^ (+ ?f (* ?g. x)) ?q) (^ (+ ?a. (* ?b. (asinh (* ?c. x)))) ?n.)) #t (asinh + +) 3 ())))
