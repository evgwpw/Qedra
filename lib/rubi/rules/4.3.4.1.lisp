(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.4.1 (a+b tan)^m (A+B tan+C tan^2).m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.3.4.1" '(
  ("Rubi 4.3.4.1 #1" (* (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?m) (+ ?A (* ?C (^ (tan (+ ?e (* ?f x))) 2)))) #t (+ tan + + tan +) 2 (2))
  ("Rubi 4.3.4.1 #2" (* (^ (+ ?a (* ?b (cot (+ ?e (* ?f x))))) ?m) (+ ?A (* ?C (^ (cot (+ ?e (* ?f x))) 2)))) #t (+ cot + + cot +) 2 (2))
  ("Rubi 4.3.4.1 #3" (* (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?m) (+ ?A (* ?B (tan (+ ?e (* ?f x)))) (* ?C (^ (tan (+ ?e (* ?f x))) 2)))) #t (+ tan + tan + + tan +) 2 (2))
  ("Rubi 4.3.4.1 #4" (* (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?m) (+ ?A (* ?C (^ (tan (+ ?e (* ?f x))) 2)))) #t (+ tan + + tan +) 2 (2))
  ("Rubi 4.3.4.1 #5" (* (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?m) (+ ?A (* ?B (tan (+ ?e (* ?f x)))) (* ?C (^ (tan (+ ?e (* ?f x))) 2)))) #t (+ tan + tan + + tan +) 2 (2))
  ("Rubi 4.3.4.1 #6" (* (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?m) (+ ?A (* ?C (^ (tan (+ ?e (* ?f x))) 2)))) #t (+ tan + + tan +) 2 (2))
  ("Rubi 4.3.4.1 #7" (/ (+ ?A (* ?B (tan (+ ?e (* ?f x)))) (* ?C (^ (tan (+ ?e (* ?f x))) 2))) (+ ?a (* ?b (tan (+ ?e (* ?f x)))))) #t (+ tan + + tan + tan +) 0 (2))
  ("Rubi 4.3.4.1 #8" (/ (+ ?A (* ?B (tan (+ ?e (* ?f x)))) (* ?C (^ (tan (+ ?e (* ?f x))) 2))) (tan (+ ?e (* ?f x)))) #t (+ tan + tan + tan +) 0 (2))
  ("Rubi 4.3.4.1 #9" (/ (+ ?A (* ?C (^ (tan (+ ?e (* ?f x))) 2))) (tan (+ ?e (* ?f x)))) #t (+ tan + tan +) 0 (2))
  ("Rubi 4.3.4.1 #10" (/ (+ ?A (* ?B (tan (+ ?e (* ?f x)))) (* ?C (^ (tan (+ ?e (* ?f x))) 2))) (+ ?a (* ?b (tan (+ ?e (* ?f x)))))) #t (+ tan + + tan + tan +) 0 (2))
  ("Rubi 4.3.4.1 #11" (/ (+ ?A (* ?C (^ (tan (+ ?e (* ?f x))) 2))) (+ ?a (* ?b (tan (+ ?e (* ?f x)))))) #t (+ tan + + tan +) 0 (2))
  ("Rubi 4.3.4.1 #12" (* (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?m) (+ ?A (* ?B (tan (+ ?e (* ?f x)))) (* ?C (^ (tan (+ ?e (* ?f x))) 2)))) #t (+ tan + tan + + tan +) 2 (2))
  ("Rubi 4.3.4.1 #13" (* (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?m) (+ ?A (* ?C (^ (tan (+ ?e (* ?f x))) 2)))) #t (+ tan + + tan +) 2 (2))
  ("Rubi 4.3.4.1 #14" (* (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?m) (+ ?A (* ?B (tan (+ ?e (* ?f x)))) (* ?C (^ (tan (+ ?e (* ?f x))) 2)))) #t (+ tan + tan + + tan +) 2 (2))
  ("Rubi 4.3.4.1 #15" (* (^ (+ ?a (* ?b (tan (+ ?e (* ?f x))))) ?m) (+ ?A (* ?C (^ (tan (+ ?e (* ?f x))) 2)))) #t (+ tan + + tan +) 2 (2))))
