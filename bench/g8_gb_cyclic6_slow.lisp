; g8: cyclic-6, grevlex — диагностика шага 21i'' (1). Полный счёт ≈ 1 мин (F#), 82 с (Lisp); эталонная реализация — 44 с. Поэтому предел
; 300 редукций: задача завершается ошибкой предела (она перехватывается — это ожидаемый результат, не сбой); меряется
; время счёта первых 300 редукций (≈ 16–20 с). Медленная задача (_slow): в общий --bench не входит, запуск — --bench g0 slow (g0 определяет gb-cyclic6).
(let ((old groebner::gb-max-reductions))
  (set! groebner::gb-max-reductions 300)
  (unwind-protect
    (try (groebner gb-cyclic6 '(a b c d e f) 'grevlex)
         (lambda (e) 'limit))
    (set! groebner::gb-max-reductions old)))
