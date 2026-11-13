(module rubi)
; Rubi 4.17.3.0 — 8 Special functions/8.7 Zeta function.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "8.7" '(
  ("Rubi 8.7 #1" (zeta 2 (+ ?a. (* ?b. x))) #t (zeta) 0 ())
  ("Rubi 8.7 #2" (zeta ?s (+ ?a. (* ?b. x))) #t (zeta) 0 ())
  ("Rubi 8.7 #3" (* (^ (+ ?c. (* ?d. x)) ?m.) (zeta 2 (+ ?a. (* ?b. x)))) #t (zeta) 2 ())
  ("Rubi 8.7 #4" (* (^ (+ ?c. (* ?d. x)) ?m.) (zeta ?s (+ ?a. (* ?b. x)))) #t (zeta) 2 ())
  ("Rubi 8.7 #5" (* (^ (+ ?c. (* ?d. x)) ?m.) (zeta ?s (+ ?a. (* ?b. x)))) #t (zeta) 2 ())))
