(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.3 (d+e x)^m (a+b arctanh(c x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "7.3.3" '(
  ("Rubi 7.3.3 #1" (/ (^ (+ ?a. (* ?b. (atanh (* ?c. x)))) ?p.) (+ ?d (* ?e. x))) #t (+ atanh) 0 ())
  ("Rubi 7.3.3 #2" (/ (^ (+ ?a. (* ?b. (acoth (* ?c. x)))) ?p.) (+ ?d (* ?e. x))) #t (+ acoth) 0 ())
  ("Rubi 7.3.3 #3" (/ (+ ?a. (* ?b. (atanh (* ?c. x)))) (+ ?d (* ?e. x))) #t (+ atanh) 0 ())
  ("Rubi 7.3.3 #4" (/ (+ ?a. (* ?b. (acoth (* ?c. x)))) (+ ?d (* ?e. x))) #t (+ acoth) 0 ())
  ("Rubi 7.3.3 #5" (/ (^ (+ ?a. (* ?b. (atanh (* ?c. x)))) 2) (+ ?d (* ?e. x))) #t (+ atanh) 0 (2))
  ("Rubi 7.3.3 #6" (/ (^ (+ ?a. (* ?b. (acoth (* ?c. x)))) 2) (+ ?d (* ?e. x))) #t (+ acoth) 0 (2))
  ("Rubi 7.3.3 #7" (/ (^ (+ ?a. (* ?b. (atanh (* ?c. x)))) 3) (+ ?d (* ?e. x))) #t (+ atanh) 0 (3))
  ("Rubi 7.3.3 #8" (/ (^ (+ ?a. (* ?b. (acoth (* ?c. x)))) 3) (+ ?d (* ?e. x))) #t (+ acoth) 0 (3))
  ("Rubi 7.3.3 #9" (* (^ (+ ?d (* ?e. x)) ?q.) (+ ?a. (* ?b. (atanh (* ?c. x))))) #t (atanh +) 2 ())
  ("Rubi 7.3.3 #10" (* (^ (+ ?d (* ?e. x)) ?q.) (+ ?a. (* ?b. (acoth (* ?c. x))))) #t (acoth +) 2 ())
  ("Rubi 7.3.3 #11" (* (^ (+ ?d (* ?e. x)) ?q.) (^ (+ ?a. (* ?b. (atanh (* ?c. x)))) ?p)) #t (atanh +) 2 ())
  ("Rubi 7.3.3 #12" (* (^ (+ ?d (* ?e. x)) ?q.) (^ (+ ?a. (* ?b. (acoth (* ?c. x)))) ?p)) #t (acoth +) 2 ())
  ("Rubi 7.3.3 #13" (/ (+ ?a. (* ?b. (atanh (* ?c. (^ x ?n))))) (+ ?d. (* ?e. x))) #t (atanh) 0 ())
  ("Rubi 7.3.3 #14" (/ (+ ?a. (* ?b. (acoth (* ?c. (^ x ?n))))) (+ ?d. (* ?e. x))) #t (acoth) 0 ())
  ("Rubi 7.3.3 #15" (/ (+ ?a. (* ?b. (atanh (* ?c. (^ x ?n))))) (+ ?d (* ?e. x))) #t (+ atanh) 0 ())
  ("Rubi 7.3.3 #16" (/ (+ ?a. (* ?b. (acoth (* ?c. (^ x ?n))))) (+ ?d (* ?e. x))) #t (+ acoth) 0 ())
  ("Rubi 7.3.3 #17" (* (^ (+ ?d. (* ?e. x)) ?m.) (+ ?a. (* ?b. (atanh (* ?c. (^ x ?n)))))) #t (atanh) 2 ())
  ("Rubi 7.3.3 #18" (* (^ (+ ?d. (* ?e. x)) ?m.) (+ ?a. (* ?b. (acoth (* ?c. (^ x ?n)))))) #t (acoth) 2 ())
  ("Rubi 7.3.3 #19" (* (^ (+ ?d (* ?e. x)) ?m.) (^ (+ ?a. (* ?b. (atanh (* ?c. (^ x ?n))))) ?p)) #t (atanh +) 2 ())
  ("Rubi 7.3.3 #20" (* (^ (+ ?d (* ?e. x)) ?m.) (^ (+ ?a. (* ?b. (acoth (* ?c. (^ x ?n))))) ?p)) #t (acoth +) 2 ())
  ("Rubi 7.3.3 #21" (* (^ (+ ?d. (* ?e. x)) ?m.) (^ (+ ?a. (* ?b. (atanh (* ?c. (^ x ?n))))) ?p.)) #t (atanh) 2 ())
  ("Rubi 7.3.3 #22" (* (^ (+ ?d. (* ?e. x)) ?m.) (^ (+ ?a. (* ?b. (acoth (* ?c. (^ x ?n))))) ?p.)) #t (acoth) 2 ())))
