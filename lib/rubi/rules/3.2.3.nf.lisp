(module rubi)
; Rubi 4.17.3.0 — 3 Logarithms/3.2.3 u log(e (f (a+b x)^p (c+d x)^q)^r)^s.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 3.2.3 #3" (* (log (* ?e. (^ (* ?f. (^ (+ ?a. (* ?b. x)) ?p.) (^ (+ ?c. (* ?d. x)) ?q.)) ?r.))) (^ (+ ?g. (* ?h. x)) -1)) (log) 2 (-1))
  ("Rubi 3.2.3 #5" (* (^ (log (* ?e. (^ (* ?f. (^ (+ ?a. (* ?b. x)) ?p.) (^ (+ ?c. (* ?d. x)) ?q.)) ?r.))) 2) (^ (+ ?g. (* ?h. x)) -1)) (log) 2 (-1 2))
  ("Rubi 3.2.3 #6" (* (^ (log (* ?e. (^ (* ?f. (^ (+ ?a. (* ?b. x)) ?p.) (^ (+ ?c. (* ?d. x)) ?q.)) ?r.))) 2) (^ (+ ?g. (* ?h. x)) -1)) (log) 2 (-1 2))
  ("Rubi 3.2.3 #8" (* (^ (+ ?s. (* ?t. (log (* ?i. (^ (+ ?g. (* ?h. x)) ?n.))))) ?m.) (log (* ?e. (^ (* ?f. (^ (+ ?a. (* ?b. x)) ?p.) (^ (+ ?c. (* ?d. x)) ?q.)) ?r.))) (^ (+ ?j. (* ?k. x)) -1)) (log log) 3 (-1))
  ("Rubi 3.2.3 #9" (* (+ ?s. (* ?t. (log (* ?i. (^ (+ ?g. (* ?h. x)) ?n.))))) (log (* ?e. (^ (* ?f. (^ (+ ?a. (* ?b. x)) ?p.) (^ (+ ?c. (* ?d. x)) ?q.)) ?r.))) (^ (+ ?j. (* ?k. x)) -1)) (log log) 3 (-1))
  ("Rubi 3.2.3 #10" (* (^ (+ ?s. (* ?t. (log (* ?i. (^ (+ ?g. (* ?h. x)) ?n.))))) ?m.) (^ (log (* ?e. (^ (* ?f. (^ (+ ?a. (* ?b. x)) ?p.) (^ (+ ?c. (* ?d. x)) ?q.)) ?r.))) ?u.) (^ (+ ?j. (* ?k. x)) -1)) (log log) 3 (-1))
  ("Rubi 3.2.3 #20" (* ?u. (^ (log (* ?e. (^ (* ?f. (+ ?g (* ?v. (^ ?w -1)))) ?r.))) ?s.)) (+ log) 1 (-1))))
