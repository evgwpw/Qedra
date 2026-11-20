(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.10 (c+d x)^m (a+b sin)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.1.10 #3" (* (sin (+ ?e. (* ?f. (Complex 0 ?fz) x))) (^ (+ ?c. (* ?d. x)) -1)) (Complex sin) 2 (-1))
  ("Rubi 4.1.10 #4" (* (sin (+ ?e. (* ?f. x))) (^ (+ ?c. (* ?d. x)) -1)) (sin) 2 (-1))
  ("Rubi 4.1.10 #5" (* (sin (+ ?e. (* ?f. (Complex 0 ?fz) x))) (^ (+ ?c. (* ?d. x)) -1)) (Complex sin) 2 (-1))
  ("Rubi 4.1.10 #6" (* (sin (+ ?e. (* ?f. (Complex 0 ?fz) x))) (^ (+ ?c. (* ?d. x)) -1)) (Complex sin) 2 (-1))
  ("Rubi 4.1.10 #7" (* (sin (+ ?e. (* ?f. x))) (^ (+ ?c. (* ?d. x)) -1)) (sin) 2 (-1))
  ("Rubi 4.1.10 #8" (* (sin (+ ?e. (* ?f. x))) (^ (+ ?c. (* ?d. x)) -1)) (sin) 2 (-1))
  ("Rubi 4.1.10 #9" (* (sin (+ ?e. (* 1/2 pi) (* ?f. x))) (^ (+ ?c. (* ?d. x)) -1/2)) (+ sin) 2 (-1/2))
  ("Rubi 4.1.10 #14" (* (^ (+ ?c. (* ?d. x)) ?m.) (^ (sin (+ ?e. (* 1/2 ?f. x))) 2)) (sin) 2 (2))
  ("Rubi 4.1.10 #25" (* (^ (+ ?c. (* ?d. x)) ?m.) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?k. pi) (* ?f. (Complex 0 ?fz) x))))) -1)) (Complex + sin +) 2 (-1))
  ("Rubi 4.1.10 #26" (* (^ (+ ?c. (* ?d. x)) ?m.) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?k. pi) (* ?f. x))))) -1)) (+ sin +) 2 (-1))
  ("Rubi 4.1.10 #27" (* (^ (+ ?c. (* ?d. x)) ?m.) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. (Complex 0 ?fz) x))))) -1)) (Complex sin +) 2 (-1))
  ("Rubi 4.1.10 #28" (* (^ (+ ?c. (* ?d. x)) ?m.) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -1)) (sin +) 2 (-1))
  ("Rubi 4.1.10 #29" (* (^ (+ ?c. (* ?d. x)) ?m.) (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) -2)) (sin +) 2 (-2))))
