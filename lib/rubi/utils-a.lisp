; rubi/utils-a.lisp — утилиты, нужные только правилам глав 1.1.2–1.1.4 (карточка A задания RUBI.CH, фаза 2).
; Файл грузит движок (lib/rubi/engine.lisp, rubi-chapter-utils) перед правилами своей главы один раз.
; Источник: Rubi 4.17.3.0 (commit 61e9c18ea248061cd83c67882f7c91a73cef912d).
; Формы IntBinomialQ на 7 и 10 аргументов (1.1.3.2.m:118, 1.1.3.4.m:89) перенесены в общий utils.lisp
; (rubi-int-binomial-q7 / -q10 и диспетчер rubi-int-binomial-q по числу аргументов); здесь пока пусто.
(module rubi)
