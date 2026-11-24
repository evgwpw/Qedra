(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.5 trig^m (a cos+b sin)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.1.5 #4" (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -1) (%sin %cos +) 0 (-1))
  ("Rubi 4.1.5 #5" (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -2) (%sin %cos +) 0 (-2))
  ("Rubi 4.1.5 #23" (* (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) ?n) (^ (%sin (+ ?c. (* ?d. x))) -1)) (%sin %sin %cos +) 2 (-1))
  ("Rubi 4.1.5 #24" (* (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) ?n) (^ (%cos (+ ?c. (* ?d. x))) -1)) (%cos %sin %cos +) 2 (-1))
  ("Rubi 4.1.5 #27" (* (%sin (+ ?c. (* ?d. x))) (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -1)) (%sin %cos + %sin) 2 (-1))
  ("Rubi 4.1.5 #28" (* (%cos (+ ?c. (* ?d. x))) (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -1)) (%sin %cos + %cos) 2 (-1))
  ("Rubi 4.1.5 #29" (* (^ (%sin (+ ?c. (* ?d. x))) ?m) (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -1)) (%sin %cos + %sin) 2 (-1))
  ("Rubi 4.1.5 #30" (* (^ (%cos (+ ?c. (* ?d. x))) ?m) (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -1)) (%sin %cos + %cos) 2 (-1))
  ("Rubi 4.1.5 #31" (* (^ (%sin (+ ?c. (* ?d. x))) -1) (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -1)) (%sin %cos + %sin) 2 (-1 -1))
  ("Rubi 4.1.5 #32" (* (^ (%cos (+ ?c. (* ?d. x))) -1) (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -1)) (%sin %cos + %cos) 2 (-1 -1))
  ("Rubi 4.1.5 #33" (* (^ (%sin (+ ?c. (* ?d. x))) ?m) (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -1)) (%sin %cos + %sin) 2 (-1))
  ("Rubi 4.1.5 #34" (* (^ (%cos (+ ?c. (* ?d. x))) ?m) (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -1)) (%sin %cos + %cos) 2 (-1))
  ("Rubi 4.1.5 #35" (* (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) ?n) (^ (%sin (+ ?c. (* ?d. x))) -1)) (%sin %sin %cos +) 2 (-1))
  ("Rubi 4.1.5 #36" (* (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) ?n) (^ (%cos (+ ?c. (* ?d. x))) -1)) (%cos %sin %cos +) 2 (-1))
  ("Rubi 4.1.5 #41" (* (^ (%cos (+ ?c. (* ?d. x))) ?m.) (^ (%sin (+ ?c. (* ?d. x))) ?n.) (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -1)) (%sin %cos + %sin %cos) 3 (-1))
  ("Rubi 4.1.5 #42" (* (^ (%cos (+ ?c. (* ?d. x))) ?m.) (^ (%sin (+ ?c. (* ?d. x))) ?n.) (^ (+ (* ?a. (%cos (+ ?c. (* ?d. x)))) (* ?b. (%sin (+ ?c. (* ?d. x))))) -1)) (%sin %cos + %sin %cos) 3 (-1))))
