(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.7 Miscellaneous/4.7.4 (c trig)^m (d trig)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 4.7.4 #26" (* (^ (* ?g. (sin (+ ?c. (* ?d. x)))) ?p) (^ (cos (+ ?a. (* ?b. x))) -1)) (cos sin) 2 (-1))
  ("Rubi 4.7.4 #27" (* (^ (* ?g. (sin (+ ?c. (* ?d. x)))) ?p) (^ (sin (+ ?a. (* ?b. x))) -1)) (sin sin) 2 (-1))))
