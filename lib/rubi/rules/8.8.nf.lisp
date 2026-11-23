(module rubi)
; Rubi 4.17.3.0 — 8 Special functions/8.8 Polylogarithm function.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 8.8 #4" (* (polylog ?n (* ?c. (^ (+ ?a. (* ?b. x)) ?p.))) (^ (+ ?d. (* ?e. x)) -1)) (polylog) 2 (-1))
  ("Rubi 8.8 #5" (* (polylog ?n (* ?a. (^ (* ?b. (^ x ?p.)) ?q.))) (^ x -1)) (polylog) 2 (-1))
  ("Rubi 8.8 #9" (* (^ (log (* ?c. (^ x ?m.))) ?r.) (polylog ?n (* ?a. (^ (* ?b. (^ x ?p.)) ?q.))) (^ x -1)) (polylog log) 3 (-1))
  ("Rubi 8.8 #11" (* (polylog 2 (* ?c. (+ ?a. (* ?b. x)))) (^ (+ ?d. (* ?e. x)) -1)) (polylog) 2 (-1))
  ("Rubi 8.8 #12" (* (polylog 2 (* ?c. (+ ?a. (* ?b. x)))) (^ (+ ?d. (* ?e. x)) -1)) (polylog) 2 (-1))
  ("Rubi 8.8 #16" (* (log (+ 1 (* ?e. x))) (polylog 2 (* ?c. x)) (^ x -1)) (polylog + log) 3 (-1))
  ("Rubi 8.8 #17" (* (+ ?g (* ?h. (log (+ 1 (* ?e. x))))) (polylog 2 (* ?c. x)) (^ x -1)) (polylog + log +) 3 (-1))))
