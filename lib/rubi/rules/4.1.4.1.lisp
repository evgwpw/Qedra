(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.4.1 (a+b sin)^m (A+B sin+C sin^2).m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.1.4.1" '(
  ("Rubi 4.1.4.1 #1" (* (^ (* ?b. (sin (+ ?e. (* ?f. x)))) ?m.) (+ (* ?B. (sin (+ ?e. (* ?f. x)))) (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin + sin) 2 (2))
  ("Rubi 4.1.4.1 #2" (* (^ (* ?b. (sin (+ ?e. (* ?f. x)))) ?m.) (+ ?A (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin + sin) 2 (2))
  ("Rubi 4.1.4.1 #3" (* (^ (* ?b. (sin (+ ?e. (* ?f. x)))) ?m) (+ ?A (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin + sin) 2 (2))
  ("Rubi 4.1.4.1 #4" (* (^ (sin (+ ?e. (* ?f. x))) ?m.) (+ ?A (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin + sin) 2 (2))
  ("Rubi 4.1.4.1 #5" (* (^ (* ?b. (sin (+ ?e. (* ?f. x)))) ?m.) (+ ?A (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin + sin) 2 (2))
  ("Rubi 4.1.4.1 #6" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m.) (+ ?A. (* ?B. (sin (+ ?e. (* ?f. x)))) (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin + sin +) 2 (2))
  ("Rubi 4.1.4.1 #7" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m.) (+ ?A. (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin +) 2 (2))
  ("Rubi 4.1.4.1 #8" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m.) (+ ?A. (* ?B. (sin (+ ?e. (* ?f. x)))) (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin + sin +) 2 (2))
  ("Rubi 4.1.4.1 #9" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m.) (+ ?A. (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin +) 2 (2))
  ("Rubi 4.1.4.1 #10" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (+ ?A. (* ?B. (sin (+ ?e. (* ?f. x)))) (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin + sin +) 2 (2))
  ("Rubi 4.1.4.1 #11" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (+ ?A. (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin +) 2 (2))
  ("Rubi 4.1.4.1 #12" (* (^ (+ ?a. (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (+ ?A. (* ?B. (sin (+ ?e. (* ?f. x)))) (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin + sin) 2 (2))
  ("Rubi 4.1.4.1 #13" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (+ ?A. (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin +) 2 (2))
  ("Rubi 4.1.4.1 #14" (* (^ (+ ?a. (* ?b. (sin (+ ?e. (* ?f. x))))) ?m.) (+ ?A. (* ?B. (sin (+ ?e. (* ?f. x)))) (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin + sin) 2 (2))
  ("Rubi 4.1.4.1 #15" (* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m.) (+ ?A. (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin +) 2 (2))
  ("Rubi 4.1.4.1 #16" (* (^ (* ?b. (^ (sin (+ ?e. (* ?f. x))) ?p)) ?m) (+ ?A. (* ?B. (sin (+ ?e. (* ?f. x)))) (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin + sin) 2 (2))
  ("Rubi 4.1.4.1 #17" (* (^ (* ?b. (^ (cos (+ ?e. (* ?f. x))) ?p)) ?m) (+ ?A. (* ?B. (cos (+ ?e. (* ?f. x)))) (* ?C. (^ (cos (+ ?e. (* ?f. x))) 2)))) #t (cos cos + cos) 2 (2))
  ("Rubi 4.1.4.1 #18" (* (^ (* ?b. (^ (sin (+ ?e. (* ?f. x))) ?p)) ?m) (+ ?A. (* ?C. (^ (sin (+ ?e. (* ?f. x))) 2)))) #t (sin sin) 2 (2))
  ("Rubi 4.1.4.1 #19" (* (^ (* ?b. (^ (cos (+ ?e. (* ?f. x))) ?p)) ?m) (+ ?A. (* ?C. (^ (cos (+ ?e. (* ?f. x))) 2)))) #t (cos cos) 2 (2))))
