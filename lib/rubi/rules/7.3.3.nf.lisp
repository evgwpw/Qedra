(module rubi)
; Rubi 4.17.3.0 — 7 Inverse hyperbolic functions/7.3 Inverse hyperbolic tangent/7.3.3 (d+e x)^m (a+b arctanh(c x^n))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Отличия единой формы (*rubi-nf* #t): ("id" образец головы мин-множителей показатели); образцы уже нормализованы (rubi-nf, tools/rubi/precompute.mjs). Файл читается только при *rubi-nf* #t.
(rubi-rules-nf-data '(
  ("Rubi 7.3.3 #1" (* (^ (+ ?a. (* ?b. (atanh (* ?c. x)))) ?p.) (^ (+ ?d (* ?e. x)) -1)) (+ atanh) 2 (-1))
  ("Rubi 7.3.3 #2" (* (^ (+ ?a. (* ?b. (acoth (* ?c. x)))) ?p.) (^ (+ ?d (* ?e. x)) -1)) (+ acoth) 2 (-1))
  ("Rubi 7.3.3 #3" (* (+ ?a. (* ?b. (atanh (* ?c. x)))) (^ (+ ?d (* ?e. x)) -1)) (+ atanh) 2 (-1))
  ("Rubi 7.3.3 #4" (* (+ ?a. (* ?b. (acoth (* ?c. x)))) (^ (+ ?d (* ?e. x)) -1)) (+ acoth) 2 (-1))
  ("Rubi 7.3.3 #5" (* (^ (+ ?a. (* ?b. (atanh (* ?c. x)))) 2) (^ (+ ?d (* ?e. x)) -1)) (+ atanh) 2 (-1 2))
  ("Rubi 7.3.3 #6" (* (^ (+ ?a. (* ?b. (acoth (* ?c. x)))) 2) (^ (+ ?d (* ?e. x)) -1)) (+ acoth) 2 (-1 2))
  ("Rubi 7.3.3 #7" (* (^ (+ ?a. (* ?b. (atanh (* ?c. x)))) 3) (^ (+ ?d (* ?e. x)) -1)) (+ atanh) 2 (-1 3))
  ("Rubi 7.3.3 #8" (* (^ (+ ?a. (* ?b. (acoth (* ?c. x)))) 3) (^ (+ ?d (* ?e. x)) -1)) (+ acoth) 2 (-1 3))
  ("Rubi 7.3.3 #13" (* (+ ?a. (* ?b. (atanh (* ?c. (^ x ?n))))) (^ (+ ?d. (* ?e. x)) -1)) (atanh) 2 (-1))
  ("Rubi 7.3.3 #14" (* (+ ?a. (* ?b. (acoth (* ?c. (^ x ?n))))) (^ (+ ?d. (* ?e. x)) -1)) (acoth) 2 (-1))
  ("Rubi 7.3.3 #15" (* (+ ?a. (* ?b. (atanh (* ?c. (^ x ?n))))) (^ (+ ?d (* ?e. x)) -1)) (+ atanh) 2 (-1))
  ("Rubi 7.3.3 #16" (* (+ ?a. (* ?b. (acoth (* ?c. (^ x ?n))))) (^ (+ ?d (* ?e. x)) -1)) (+ acoth) 2 (-1))))
