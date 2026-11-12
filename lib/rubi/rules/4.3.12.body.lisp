(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.12 (d+e x)^m tan(a+b x+c x^2)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Тела правил: ("id" условие правая-часть); читаются лениво (rubi-load-bodies).
(rubi-bodies-data '(
  ("Rubi 4.3.12 #1" (rubi::rubi-freeq (list ?a ?b ?c ?n) (quote x)) (rubi::rubi-unintegrable (^ (tan (+ a (* b (quote x)) (* c (^ (quote x) 2)))) n) (quote x)))
  ("Rubi 4.3.12 #2" (rubi::rubi-freeq (list ?a ?b ?c ?n) (quote x)) (rubi::rubi-unintegrable (^ (cot (+ a (* b (quote x)) (* c (^ (quote x) 2)))) n) (quote x)))
  ("Rubi 4.3.12 #3" (and (not (equal? ?d 0)) (and (rubi::rubi-freeq (list ?a ?b ?c ?d ?e) (quote x)) (rubi::rubi-eqq (- (* (* 2 ?c) ?d) (* ?b ?e)) 0))) (/ (* (- e) (log (cos (+ a (* b (quote x)) (* c (^ (quote x) 2)))))) (* 2 c)))
  ("Rubi 4.3.12 #4" (and (not (equal? ?d 0)) (and (rubi::rubi-freeq (list ?a ?b ?c ?d ?e) (quote x)) (rubi::rubi-eqq (- (* (* 2 ?c) ?d) (* ?b ?e)) 0))) (/ (* e (log (sin (+ a (* b (quote x)) (* c (^ (quote x) 2)))))) (* 2 c)))
  ("Rubi 4.3.12 #5" (and (rubi::rubi-freeq (list ?a ?b ?c ?d ?e) (quote x)) (rubi::rubi-neq (- (* (* 2 ?c) ?d) (* ?b ?e)) 0)) (+ (/ (* (- e) (log (cos (+ a (* b (quote x)) (* c (^ (quote x) 2)))))) (* 2 c)) (* (/ (- (* 2 c d) (* b e)) (* 2 c)) (rubi::rubi-int (tan (+ a (* b (quote x)) (* c (^ (quote x) 2)))) (tan (+ a (* b (quote x)) (* c (^ (quote x) 2)))) (quote x)))))
  ("Rubi 4.3.12 #6" (and (rubi::rubi-freeq (list ?a ?b ?c ?d ?e) (quote x)) (rubi::rubi-neq (- (* (* 2 ?c) ?d) (* ?b ?e)) 0)) (+ (/ (* e (log (sin (+ a (* b (quote x)) (* c (^ (quote x) 2)))))) (* 2 c)) (* (/ (- (* 2 c d) (* b e)) (* 2 c)) (rubi::rubi-int (cot (+ a (* b (quote x)) (* c (^ (quote x) 2)))) (cot (+ a (* b (quote x)) (* c (^ (quote x) 2)))) (quote x)))))
  ("Rubi 4.3.12 #7" (rubi::rubi-freeq (list ?a ?b ?c ?d ?e ?m ?n) (quote x)) (rubi::rubi-unintegrable (* (^ (+ d (* e (quote x))) m) (^ (tan (+ a (* b (quote x)) (* c (^ (quote x) 2)))) n)) (quote x)))
  ("Rubi 4.3.12 #8" (rubi::rubi-freeq (list ?a ?b ?c ?d ?e ?m ?n) (quote x)) (rubi::rubi-unintegrable (* (^ (+ d (* e (quote x))) m) (^ (cot (+ a (* b (quote x)) (* c (^ (quote x) 2)))) n)) (quote x)))))
