(module rubi)
; Rubi 4.17.3.0 — 8 Special functions/8.10 Bessel functions.m
; Copyright (c) 2018 Rule-Based-Integration Organization (MIT); текст лицензии — lib/rubi/LICENSE-RUBI.txt
; Сгенерировано tools/rubi из github.com/RuleBasedIntegration/Rubi @ 61e9c18ea248061cd83c67882f7c91a73cef912d; не править руками.
; Данные для индекса: ("id" образец есть-условие обязательные-головы мин-множителей показатели); образец нормализован (tools/rubi/precompute.mjs); условия и правые части - в <файл>.body.lisp.
(rubi-rules-data "8.10" '(
  ("Rubi 8.10 #1" (bessel-j 1 (+ ?a (* ?b x))) #t (+ bessel-j) 0 ())
  ("Rubi 8.10 #2" (bessel-j ?n (+ ?a (* ?b x))) #t (+ bessel-j) 0 ())
  ("Rubi 8.10 #3" (bessel-j ?n (+ ?a (* ?b x))) #t (+ bessel-j) 0 ())))
