(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.6 (a+b cos+c sin)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.1.6 #3" (^ (+ ?a (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1) (sin cos +) 0 (-1))
  ("Rubi 4.1.6 #10" (^ (+ ?a (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1) (sin cos +) 0 (-1))
  ("Rubi 4.1.6 #11" (^ (+ ?a (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1) (sin cos +) 0 (-1))
  ("Rubi 4.1.6 #12" (^ (+ ?a (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1) (sin cos +) 0 (-1))
  ("Rubi 4.1.6 #13" (^ (+ ?a (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1) (sin cos +) 0 (-1))
  ("Rubi 4.1.6 #17" (^ (+ ?a (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -3/2) (sin cos +) 0 (-3/2))
  ("Rubi 4.1.6 #19" (* (+ ?A. (* ?B. (cos (+ ?d. (* ?e. x)))) (* ?C. (sin (+ ?d. (* ?e. x))))) (^ (+ ?a (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1)) (sin cos + sin cos +) 2 (-1))
  ("Rubi 4.1.6 #20" (* (+ ?A. (* ?C. (sin (+ ?d. (* ?e. x))))) (^ (+ ?a (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1)) (sin cos + sin) 2 (-1))
  ("Rubi 4.1.6 #21" (* (+ ?A. (* ?B. (cos (+ ?d. (* ?e. x))))) (^ (+ ?a (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1)) (sin cos + cos) 2 (-1))
  ("Rubi 4.1.6 #22" (* (+ ?A. (* ?B. (cos (+ ?d. (* ?e. x)))) (* ?C. (sin (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1)) (sin cos + sin cos +) 2 (-1))
  ("Rubi 4.1.6 #23" (* (+ ?A. (* ?C. (sin (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1)) (sin cos + sin) 2 (-1))
  ("Rubi 4.1.6 #24" (* (+ ?A. (* ?B. (cos (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1)) (sin cos + cos) 2 (-1))
  ("Rubi 4.1.6 #25" (* (+ ?A. (* ?B. (cos (+ ?d. (* ?e. x)))) (* ?C. (sin (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1)) (sin cos + sin cos +) 2 (-1))
  ("Rubi 4.1.6 #26" (* (+ ?A. (* ?C. (sin (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1)) (sin cos + sin) 2 (-1))
  ("Rubi 4.1.6 #27" (* (+ ?A. (* ?B. (cos (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -1)) (sin cos + cos) 2 (-1))
  ("Rubi 4.1.6 #39" (* (+ ?A. (* ?B. (cos (+ ?d. (* ?e. x)))) (* ?C. (sin (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -2)) (sin cos + sin cos +) 2 (-2))
  ("Rubi 4.1.6 #40" (* (+ ?A. (* ?C. (sin (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -2)) (sin cos + sin) 2 (-2))
  ("Rubi 4.1.6 #41" (* (+ ?A. (* ?B. (cos (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -2)) (sin cos + cos) 2 (-2))
  ("Rubi 4.1.6 #42" (* (+ ?A. (* ?B. (cos (+ ?d. (* ?e. x)))) (* ?C. (sin (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -2)) (sin cos + sin cos +) 2 (-2))
  ("Rubi 4.1.6 #43" (* (+ ?A. (* ?C. (sin (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -2)) (sin cos + sin) 2 (-2))
  ("Rubi 4.1.6 #44" (* (+ ?A. (* ?B. (cos (+ ?d. (* ?e. x))))) (^ (+ ?a. (* ?b. (cos (+ ?d. (* ?e. x)))) (* ?c. (sin (+ ?d. (* ?e. x))))) -2)) (sin cos + cos) 2 (-2))
  ("Rubi 4.1.6 #48" (^ (+ ?a. (* ?b. (sec (+ ?d. (* ?e. x)))) (* ?c. (tan (+ ?d. (* ?e. x))))) -1) (tan sec +) 0 (-1))
  ("Rubi 4.1.6 #49" (^ (+ ?a. (* ?b. (csc (+ ?d. (* ?e. x)))) (* ?c. (cot (+ ?d. (* ?e. x))))) -1) (cot csc +) 0 (-1))))
