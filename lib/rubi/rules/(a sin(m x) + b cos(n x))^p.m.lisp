(module rubi)
; Rubi 4.17.3.0 — 4 Trig functions/4.7 Miscellaneous/(a sin(m x) + b cos(n x))^p.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "(a sin(m x) + b cos(n x))^p.m" '(
  ("Rubi (a sin(m x) + b cos(n x))^p.m #1" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (sin (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (sin sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #2" (^ (+ (* ?a. (cos (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos cos +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #3" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (sin (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (sin sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #4" (^ (+ (* ?a. (cos (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos cos +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #5" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (sin (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (sin sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #6" (^ (+ (* ?a. (cos (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos cos +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #7" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (sin (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (sin sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #8" (^ (+ (* ?a. (cos (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos cos +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #9" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #10" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #11" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #12" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (sin (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (sin sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #13" (^ (+ (* ?a. (cos (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos cos +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #14" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (sin (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (sin sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #15" (^ (+ (* ?a. (cos (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos cos +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #16" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (sin (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (sin sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #17" (^ (+ (* ?a. (cos (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos cos +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #18" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (sin (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (sin sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #19" (^ (+ (* ?a. (cos (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos cos +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #20" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #21" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos sin +) 0 ())
  ("Rubi (a sin(m x) + b cos(n x))^p.m #22" (^ (+ (* ?a. (sin (* ?m. (+ ?c. (* ?d. x))))) (* ?b. (cos (* ?n. (+ ?c. (* ?d. x)))))) ?p) #t (cos sin +) 0 ())))
