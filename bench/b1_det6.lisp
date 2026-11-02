; b1: определитель 6x6, численная матрица
(define (b1-row i)
  (map (lambda (j) (+ 1 (mod (* (+ i 2) (+ j 3) (+ i j 1)) 13))) (range 6)))
(det (tensor (map b1-row (range 6))))
