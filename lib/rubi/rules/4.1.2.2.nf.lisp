(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.2.2 (g cos)^p (a+b sin)^m (c+d sin)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.1.2.2 #3" (* (^ (cos (+ ?e. (* ?f. x))) ?p) (^ (* ?d. (sin (+ ?e. (* ?f. x)))) ?n.) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))
  ("Rubi 4.1.2.2 #7" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (* ?d. (sin (+ ?e. (* ?f. x)))) ?n.) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))
  ("Rubi 4.1.2.2 #10" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1/2) (^ (+ ?c (* ?d. (sin (+ ?e. (* ?f. x))))) -1/2)) (sin + sin + cos) 3 (-1/2 -1/2))
  ("Rubi 4.1.2.2 #35" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (+ ?c. (* ?d. (sin (+ ?e. (* ?f. x))))) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))
  ("Rubi 4.1.2.2 #66" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (sin (+ ?e. (* ?f. x))) ?n) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))
  ("Rubi 4.1.2.2 #67" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (* ?d. (sin (+ ?e. (* ?f. x)))) ?n) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))
  ("Rubi 4.1.2.2 #68" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (* ?d. (sin (+ ?e. (* ?f. x)))) ?n) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))
  ("Rubi 4.1.2.2 #69" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (* ?d. (sin (+ ?e. (* ?f. x)))) ?n) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))
  ("Rubi 4.1.2.2 #70" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (* ?d. (sin (+ ?e. (* ?f. x)))) ?n) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))
  ("Rubi 4.1.2.2 #71" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (* ?d. (sin (+ ?e. (* ?f. x)))) ?n) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))
  ("Rubi 4.1.2.2 #72" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (* ?d. (sin (+ ?e. (* ?f. x)))) ?n) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))
  ("Rubi 4.1.2.2 #73" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) 1/2) (^ (sin (+ ?e. (* ?f. x))) -1/2) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1 -1/2 1/2))
  ("Rubi 4.1.2.2 #74" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) 1/2) (^ (* ?d (sin (+ ?e. (* ?f. x)))) -1/2) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1 -1/2 1/2))
  ("Rubi 4.1.2.2 #75" (* (^ (* ?d. (sin (+ ?e. (* ?f. x)))) 1/2) (^ (cos (+ ?e. (* ?f. x))) -1/2) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + cos sin) 3 (-1 -1/2 1/2))
  ("Rubi 4.1.2.2 #76" (* (^ (* ?d. (sin (+ ?e. (* ?f. x)))) 1/2) (^ (* ?g. (cos (+ ?e. (* ?f. x)))) -1/2) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + cos sin) 3 (-1 -1/2 1/2))
  ("Rubi 4.1.2.2 #77" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (* ?d. (sin (+ ?e. (* ?f. x)))) ?n) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))
  ("Rubi 4.1.2.2 #78" (* (^ (* ?g. (cos (+ ?e. (* ?f. x)))) ?p) (^ (* ?d. (sin (+ ?e. (* ?f. x)))) ?n) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin + sin cos) 3 (-1))))
