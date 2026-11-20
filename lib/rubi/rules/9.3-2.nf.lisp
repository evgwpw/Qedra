(module rubi)
; Rubi 4.17.3.0 — 9 Miscellaneous/9.3 Piecewise linear functions.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 9.3-2 #2" (* ?v (^ ?u -1)) () 1 (-1))
  ("Rubi 9.3-2 #3" (* (^ ?v ?n) (^ ?u -1)) () 2 (-1))
  ("Rubi 9.3-2 #4" (* (^ ?u -1) (^ ?v -1)) () 2 (-1 -1))
  ("Rubi 9.3-2 #7" (* (^ ?v ?n) (^ ?u -1)) () 2 (-1))
  ("Rubi 9.3-2 #8" (* (^ ?v ?n) (^ ?u -1)) () 2 (-1))))
