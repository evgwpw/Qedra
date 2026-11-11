(module rubi)
; Rubi 4.17.3.0 — 9 Miscellaneous/9.1 Derivative integration rules.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "9.1" '(
  ("Rubi 9.1 #1" (x) #t (x) 0 ())
  ("Rubi 9.1 #2" (* (^ (* ?c (^ ?F (+ ?a (* ?b x)))) ?p) (x)) #t (x +) 2 ())
  ("Rubi 9.1 #3" (* (^ (* ?c (^ ?F (+ ?a (* ?b x)))) ?p) (x)) #t (x +) 2 ())
  ("Rubi 9.1 #4" (* (sin (+ ?a (* ?b x))) (x)) #t (x + sin) 2 ())
  ("Rubi 9.1 #5" (* (cos (+ ?a (* ?b x))) (x)) #t (x + cos) 2 ())
  ("Rubi 9.1 #6" (* (sin (+ ?a (* ?b x))) (x)) #t (x + sin) 2 ())
  ("Rubi 9.1 #7" (* (cos (+ ?a (* ?b x))) (x)) #t (x + cos) 2 ())
  ("Rubi 9.1 #8" (* ?u (x)) #t (x) 1 ())
  ("Rubi 9.1 #9" (* ?u (+ (* ?a (x) (?g x)) (* ?a (?f x) (x)))) #t (x x +) 1 ())
  ("Rubi 9.1 #10" (* ?u (+ (* ?a (x) (?g x)) (* ?a (x) (x)))) #t (x x x +) 1 ())
  ("Rubi 9.1 #11" (* ?u (+ (* ?a (x) (x)) (* ?a (x) (x)))) #t (x x x x +) 1 ())
  ("Rubi 9.1 #12" (* ?u (^ (?f x) ?p) (+ (* ?a (x) (?g x)) (* ?b (?f x) (x)))) #t (x x +) 2 ())
  ("Rubi 9.1 #13" (* ?u (^ (x) ?p) (+ (* ?a (x) (?g x)) (* ?b (x) (x)))) #t (x x x + x) 2 ())
  ("Rubi 9.1 #14" (* ?u (^ (?g x) ?q) (+ (* ?a (x) (?g x)) (* ?b (x) (x)))) #t (x x x +) 2 ())
  ("Rubi 9.1 #15" (* ?u (^ (x) ?p) (+ (* ?a (x) (x)) (* ?b (x) (x)))) #t (x x x x + x) 2 ())
  ("Rubi 9.1 #16" (* ?u (^ (?f x) ?p) (^ (?g x) ?q) (+ (* ?a (x) (?g x)) (* ?b (?f x) (x)))) #t (x x +) 3 ())
  ("Rubi 9.1 #17" (* ?u (^ (x) ?p) (^ (?g x) ?q) (+ (* ?a (x) (?g x)) (* ?b (x) (x)))) #t (x x x + x) 3 ())
  ("Rubi 9.1 #18" (* ?u (^ (x) ?p) (^ (x) ?q) (+ (* ?a (x) (x)) (* ?b (x) (x)))) #t (x x x x + x x) 3 ())
  ("Rubi 9.1 #19" (+ (* (x) (?g x)) (* (?f x) (x))) #t (x x +) 0 ())
  ("Rubi 9.1 #20" (/ (- (* (x) (?g x)) (* (?f x) (x))) (^ (?g x) 2)) #t (x x) 0 (2))
  ("Rubi 9.1 #21" (/ (- (* (x) (?g x)) (* (?f x) (x))) (* (?f x) (?g x))) #t (x x) 0 ())))
