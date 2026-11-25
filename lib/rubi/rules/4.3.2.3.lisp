(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.3 Tangent/4.3.2.3 (g tan)^p (a+b tan)^m (c+d tan)^n.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "4.3.2.3" '(
  ("Rubi 4.3.2.3 #1" (* (^ (* ?g. (tan (+ ?e. (* ?f. x)))) ?p.) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) ?m) (^ (+ ?c (* ?d. (tan (+ ?e. (* ?f. x))))) ?n)) #t (tan + tan + tan) 3 ())
  ("Rubi 4.3.2.3 #2" (* (^ (* ?g. (cot (+ ?e. (* ?f. x)))) ?p) (^ (+ ?a. (* ?b. (tan (+ ?e. (* ?f. x))))) ?m.) (^ (+ ?c (* ?d. (tan (+ ?e. (* ?f. x))))) ?n.)) #t (tan + tan cot) 3 ())
  ("Rubi 4.3.2.3 #3" (* (^ (* ?g. (tan (+ ?e. (* ?f. x)))) ?p) (^ (+ ?a. (* ?b. (cot (+ ?e. (* ?f. x))))) ?m.) (^ (+ ?c (* ?d. (cot (+ ?e. (* ?f. x))))) ?n.)) #t (cot + cot tan) 3 ())
  ("Rubi 4.3.2.3 #4" (* (^ (* ?g. (^ (tan (+ ?e. (* ?f. x))) ?q)) ?p) (^ (+ ?a. (* ?b. (tan (+ ?e. (* ?f. x))))) ?m.) (^ (+ ?c (* ?d. (tan (+ ?e. (* ?f. x))))) ?n.)) #t (tan + tan tan) 3 ())
  ("Rubi 4.3.2.3 #5" (* (^ (* ?g. (tan (+ ?e. (* ?f. x)))) ?p.) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) ?m.) (^ (+ ?c (* ?d. (cot (+ ?e. (* ?f. x))))) ?n.)) #t (cot + tan + tan) 3 ())
  ("Rubi 4.3.2.3 #6" (* (^ (tan (+ ?e. (* ?f. x))) ?p.) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) ?m.) (^ (+ ?c (* ?d. (cot (+ ?e. (* ?f. x))))) ?n)) #t (cot + tan + tan) 3 ())
  ("Rubi 4.3.2.3 #7" (* (^ (* ?g. (tan (+ ?e. (* ?f. x)))) ?p) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) ?m.) (^ (+ ?c (* ?d. (cot (+ ?e. (* ?f. x))))) ?n)) #t (cot + tan + tan) 3 ())
  ("Rubi 4.3.2.3 #8" (* (^ (* ?g. (tan (+ ?e. (* ?f. x)))) ?p.) (^ (+ ?a (* ?b. (tan (+ ?e. (* ?f. x))))) ?m) (^ (+ ?c (* ?d. (cot (+ ?e. (* ?f. x))))) ?n)) #t (cot + tan + tan) 3 ())))
