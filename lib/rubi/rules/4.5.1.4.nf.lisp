(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.5 Secant/4.5.1.4 (d tan)^n (a+b sec)^m.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.5.1.4 #5" (* (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) (^ (cot (+ ?c. (* ?d. x))) -1)) (cot csc +) 2 (-1))
  ("Rubi 4.5.1.4 #13" (* (^ (* ?e. (cot (+ ?c. (* ?d. x)))) ?m) (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) -1)) (csc + cot) 2 (-1))
  ("Rubi 4.5.1.4 #15" (* (^ (* ?e. (cot (+ ?c. (* ?d. x)))) ?m) (^ (+ ?a (* ?b. (csc (+ ?c. (* ?d. x))))) -1)) (csc + cot) 2 (-1))))
