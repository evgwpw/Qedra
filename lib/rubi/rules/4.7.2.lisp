(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.7 Miscellaneous/4.7.2 Tangent normalization rules.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.7.2" '(
  ("Rubi 4.7.2 #1" (* ?u (^ (* ?c (cot (+ ?a (* ?b x)))) ?m) (^ (* ?d (tan (+ ?a (* ?b x)))) ?n)) #t (+ tan + cot) 2 ())
  ("Rubi 4.7.2 #2" (* ?u (^ (* ?c (tan (+ ?a (* ?b x)))) ?m) (^ (* ?d (cos (+ ?a (* ?b x)))) ?n)) #t (+ cos + tan) 2 ())
  ("Rubi 4.7.2 #3" (* ?u (^ (* ?c (cot (+ ?a (* ?b x)))) ?m)) #t (+ cot) 1 ())
  ("Rubi 4.7.2 #4" (* ?u (^ (* ?c (tan (+ ?a (* ?b x)))) ?m)) #t (+ tan) 1 ())
  ("Rubi 4.7.2 #5" (* ?u (^ (* ?c (tan (+ ?a (* ?b x)))) ?n) (+ ?A (* ?B (cot (+ ?a (* ?b x)))))) #t (+ cot + + tan) 2 ())
  ("Rubi 4.7.2 #6" (* ?u (^ (* ?c (cot (+ ?a (* ?b x)))) ?n) (+ ?A (* ?B (tan (+ ?a (* ?b x)))))) #t (+ tan + + cot) 2 ())
  ("Rubi 4.7.2 #7" (* ?u (+ ?A (* ?B (cot (+ ?a (* ?b x)))))) #t (+ cot +) 1 ())
  ("Rubi 4.7.2 #8" (* ?u (+ ?A (* ?B (tan (+ ?a (* ?b x)))))) #t (+ tan +) 1 ())
  ("Rubi 4.7.2 #9" (* ?u (^ (* ?c (tan (+ ?a (* ?b x)))) ?n) (+ ?A (* ?B (cot (+ ?a (* ?b x)))) (* ?C (^ (cot (+ ?a (* ?b x))) 2)))) #t (+ cot + cot + + tan) 2 (2))
  ("Rubi 4.7.2 #10" (* ?u (^ (* ?c (cot (+ ?a (* ?b x)))) ?n) (+ ?A (* ?B (tan (+ ?a (* ?b x)))) (* ?C (^ (tan (+ ?a (* ?b x))) 2)))) #t (+ tan + tan + + cot) 2 (2))
  ("Rubi 4.7.2 #11" (* ?u (^ (* ?c (tan (+ ?a (* ?b x)))) ?n) (+ ?A (* ?C (^ (cot (+ ?a (* ?b x))) 2)))) #t (+ cot + + tan) 2 (2))
  ("Rubi 4.7.2 #12" (* ?u (^ (* ?c (cot (+ ?a (* ?b x)))) ?n) (+ ?A (* ?C (^ (tan (+ ?a (* ?b x))) 2)))) #t (+ tan + + cot) 2 (2))
  ("Rubi 4.7.2 #13" (* ?u (+ ?A (* ?B (cot (+ ?a (* ?b x)))) (* ?C (^ (cot (+ ?a (* ?b x))) 2)))) #t (+ cot + cot +) 1 (2))
  ("Rubi 4.7.2 #14" (* ?u (+ ?A (* ?B (tan (+ ?a (* ?b x)))) (* ?C (^ (tan (+ ?a (* ?b x))) 2)))) #t (+ tan + tan +) 1 (2))
  ("Rubi 4.7.2 #15" (* ?u (+ ?A (* ?C (^ (cot (+ ?a (* ?b x))) 2)))) #t (+ cot +) 1 (2))
  ("Rubi 4.7.2 #16" (* ?u (+ ?A (* ?C (^ (tan (+ ?a (* ?b x))) 2)))) #t (+ tan +) 1 (2))
  ("Rubi 4.7.2 #17" (* ?u (+ ?A (* ?B (tan (+ ?a (* ?b x)))) (* ?C (cot (+ ?a (* ?b x)))))) #t (+ cot + tan +) 1 ())
  ("Rubi 4.7.2 #18" (* ?u (+ (* ?A (^ (tan (+ ?a (* ?b x))) ?n)) (* ?B (^ (tan (+ ?a (* ?b x))) ?n1)) (* ?C (^ (tan (+ ?a (* ?b x))) ?n2)))) #t (+ tan + tan + tan +) 1 ())
  ("Rubi 4.7.2 #19" (* ?u (+ (* ?A (^ (cot (+ ?a (* ?b x))) ?n)) (* ?B (^ (cot (+ ?a (* ?b x))) ?n1)) (* ?C (^ (cot (+ ?a (* ?b x))) ?n2)))) #t (+ cot + cot + cot +) 1 ())))
