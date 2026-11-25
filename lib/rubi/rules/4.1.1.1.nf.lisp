(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.1 Sine/4.1.1.1 (a+b sin)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.1.1.1 #2" (^ (sin (+ ?c. (* 1/2 ?d. x))) 2) (sin) 0 (2))
  ("Rubi 4.1.1.1 #5" (sin (+ ?c. (* 1/2 pi) (* ?d. x))) (+ sin) 0 ())
  ("Rubi 4.1.1.1 #15" (^ (+ ?a (* ?b. (sin (+ ?c. (* ?d. x))))) -1) (sin +) 0 (-1))
  ("Rubi 4.1.1.1 #24" (^ (+ ?a (* ?b. (sin (+ ?c. (* ?d. x))))) -1) (sin +) 0 (-1))
  ("Rubi 4.1.1.1 #25" (^ (+ ?a (* ?b. (sin (+ ?c. (* ?d. x))))) -1) (sin +) 0 (-1))
  ("Rubi 4.1.1.1 #26" (^ (+ ?a (* ?b. (sin (+ ?c. (* 1/2 pi) (* ?d. x))))) -1) (+ sin +) 0 (-1))
  ("Rubi 4.1.1.1 #27" (^ (+ ?a (* ?b. (sin (+ ?c. (* ?d. x))))) -1) (sin +) 0 (-1))))
