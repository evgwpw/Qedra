; d2: чистый Lisp — map/filter/foldl по списку из 10^5 элементов
(foldl + 0 (filter (lambda (x) (= (mod x 3) 0)) (map (lambda (x) (* x 2)) (range 100000))))
