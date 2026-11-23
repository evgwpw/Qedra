(module rubi)
; Rubi 4.17.3.0 — 3 Logarithms/3.5 Miscellaneous logarithms.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 3.5 #4" (* (+ ?a. (* ?b. (log (* ?c. (^ (log (* ?d. (^ x ?n.))) ?p.))))) (^ x -1)) (log log) 2 (-1))
  ("Rubi 3.5 #7" (* (^ (+ ?a. (* ?b. (log (* ?c. (^ ?RFx ?p.))))) ?n.) (^ (+ ?d. (* ?e. x)) -1)) (log) 2 (-1))
  ("Rubi 3.5 #9" (* (log (* ?c. (^ ?RFx ?n.))) (^ (+ ?d (* ?e. (^ x 2))) -1)) (+ log) 2 (2 -1))
  ("Rubi 3.5 #10" (* (log (* ?c. (^ ?Px ?n.))) (^ ?Qx -1)) (log) 2 (-1))
  ("Rubi 3.5 #21" (* (^ (log (* ?c. (^ x ?n.))) ?r.) (^ x -1) (^ (+ (* ?a. (^ x ?m.)) (* ?b. (^ (log (* ?c. (^ x ?n.))) ?q))) -1)) (log + log) 3 (-1 -1))
  ("Rubi 3.5 #22" (* (^ (log (* ?c. (^ x ?n.))) ?r.) (^ (+ (* ?a. (^ x ?m.)) (* ?b. (^ (log (* ?c. (^ x ?n.))) ?q))) ?p.) (^ x -1)) (log + log) 3 (-1))
  ("Rubi 3.5 #23" (* (^ (log (* ?c. (^ x ?n.))) ?r.) (^ (+ (* ?a. (^ x ?m.)) (* ?b. (^ (log (* ?c. (^ x ?n.))) ?q))) ?p.) (^ x -1)) (log + log) 3 (-1))
  ("Rubi 3.5 #24" (* (+ (* ?d. (^ x ?m.)) (* ?e. (^ (log (* ?c. (^ x ?n.))) ?r.))) (^ x -1) (^ (+ (* ?a. (^ x ?m.)) (* ?b. (^ (log (* ?c. (^ x ?n.))) ?q))) -1)) (log + log +) 3 (-1 -1))
  ("Rubi 3.5 #25" (* (+ ?u (* ?d. (^ x ?m.)) (* ?e. (^ (log (* ?c. (^ x ?n.))) ?r.))) (^ x -1) (^ (+ (* ?a. (^ x ?m.)) (* ?b. (^ (log (* ?c. (^ x ?n.))) ?q))) -1)) (log + log +) 3 (-1 -1))
  ("Rubi 3.5 #26" (* (+ (* ?d. (^ x ?m.)) (* ?e. (^ (log (* ?c. (^ x ?n.))) ?r.))) (^ x -1) (^ (+ (* ?a. (^ x ?m.)) (* ?b. (^ (log (* ?c. (^ x ?n.))) ?q))) -1)) (log + log +) 3 (-1 -1))
  ("Rubi 3.5 #27" (* (+ (* ?d. (^ x ?m.)) (* ?e. (^ (log (* ?c. (^ x ?n.))) ?r.))) (^ (+ (* ?a. (^ x ?m.)) (* ?b. (^ (log (* ?c. (^ x ?n.))) ?q))) ?p.) (^ x -1)) (log + log +) 3 (-1))
  ("Rubi 3.5 #28" (* (+ (* ?d. (^ x ?m.)) (* ?e. (^ (log (* ?c. (^ x ?n.))) ?r.))) (^ (+ (* ?a. (^ x ?m.)) (* ?b. (^ (log (* ?c. (^ x ?n.))) ?q))) ?p.) (^ x -1)) (log + log +) 3 (-1))
  ("Rubi 3.5 #29" (* (+ (* ?d. (^ x ?m.)) (* ?e. (^ x ?m.) (log (* ?c. (^ x ?n.)))) (* ?f. (^ (log (* ?c. (^ x ?n.))) ?q.))) (^ x -1) (^ (+ (* ?a. (^ x ?m.)) (* ?b. (^ (log (* ?c. (^ x ?n.))) ?q))) -2)) (log + log log +) 3 (-2 -1))
  ("Rubi 3.5 #30" (* (+ ?d (* ?e. (log (* ?c. (^ x ?n.))))) (^ (+ (* ?a. x) (* ?b. (^ (log (* ?c. (^ x ?n.))) ?q))) -2)) (log + log +) 2 (-2))
  ("Rubi 3.5 #33" (* (log ?u) (^ (+ ?a. (* ?b. x)) -1)) (log) 2 (-1))
  ("Rubi 3.5 #35" (* (log ?u) (^ ?Qx -1)) (log) 2 (-1))))
