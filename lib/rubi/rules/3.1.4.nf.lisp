(module rubi)
; Rubi 4.17.3.0 — 3 Logarithms/3.1.4 (f x)^m (d+e x^r)^q (a+b log(c x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 3.1.4 #1" (* (^ x ?m.) (^ (+ ?d (* ?e. (^ x -1))) ?q.) (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.)) (log +) 3 (-1))
  ("Rubi 3.1.4 #6" (* (^ (* ?f. x) ?m.) (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.) (^ (+ ?d (* ?e. (^ x ?r))) -1)) (+ log) 3 (-1))
  ("Rubi 3.1.4 #9" (* (+ ?a. (* ?b. (log (* ?c. (^ x ?n))))) (^ x -1) (^ (+ ?d (* ?e. (^ x ?r.))) -1)) (+ log) 3 (-1 -1))
  ("Rubi 3.1.4 #10" (* (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.) (^ x -1) (^ (+ ?d (* ?e. (^ x ?r.))) -1)) (+ log) 3 (-1 -1))
  ("Rubi 3.1.4 #11" (* (^ x ?m.) (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.) (^ (+ ?d (* ?e. (^ x ?r.))) -1)) (+ log) 3 (-1))
  ("Rubi 3.1.4 #19" (* (^ (+ ?d (* ?e. x)) ?q.) (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.) (^ x -1)) (log +) 3 (-1))
  ("Rubi 3.1.4 #20" (* (^ (+ ?d (* ?e. x)) ?q) (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.) (^ x -1)) (log +) 3 (-1))
  ("Rubi 3.1.4 #21" (* (^ (+ ?d (* ?e. (^ x ?r.))) ?q.) (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) (^ x -1)) (log +) 3 (-1))
  ("Rubi 3.1.4 #22" (* (^ (+ ?d (* ?e. (^ x ?r.))) ?q) (^ (+ ?a. (* ?b. (log (* ?c. (^ x ?n.))))) ?p.) (^ x -1)) (log +) 3 (-1))))
