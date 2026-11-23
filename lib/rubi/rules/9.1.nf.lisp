(module rubi)
; Rubi 4.17.3.0 — 9 Miscellaneous/9.1 Derivative integration rules.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 9.1 #10" (* ?u (+ (* ?a. (x) (?g x)) (* ?a. (^ (x) 2)))) (x x +) 1 (2))
  ("Rubi 9.1 #11" (* 2 ?u ?a. (^ (x) 2)) (x) 2 (2))
  ("Rubi 9.1 #13" (* ?u (^ (x) ?p.) (+ (* ?a. (x) (?g x)) (* ?b. (^ (x) 2)))) (x x + x) 2 (2))
  ("Rubi 9.1 #14" (* ?u (^ (?g x) ?q.) (+ (* ?a. (x) (?g x)) (* ?b. (^ (x) 2)))) (x x +) 2 (2))
  ("Rubi 9.1 #15" (* ?u (^ (x) ?p.) (+ (* ?a. (^ (x) 2)) (* ?b. (^ (x) 2)))) (x x + x) 2 (2 2))
  ("Rubi 9.1 #17" (* ?u (^ (x) ?p.) (^ (?g x) ?q.) (+ (* ?a. (x) (?g x)) (* ?b. (^ (x) 2)))) (x x + x) 3 (2))
  ("Rubi 9.1 #18" (* ?u (^ (x) (+ ?p. ?q.)) (+ (* ?a. (^ (x) 2)) (* ?b. (^ (x) 2)))) (x x + x) 2 (2 2))
  ("Rubi 9.1 #20" (* (+ (* (x) (?g x)) (* -1 (?f x) (x))) (^ (?g x) -2)) (x x +) 2 (-2))
  ("Rubi 9.1 #21" (* (+ (* (x) (?g x)) (* -1 (?f x) (x))) (^ (?f x) -1) (^ (?g x) -1)) (x x +) 3 (-1 -1))))
