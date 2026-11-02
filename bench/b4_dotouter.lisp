; b4: dot векторов длины 200 и outer 20x20
(define b4-u (map (lambda (i) (+ i 1)) (range 200)))
(define b4-v (map (lambda (i) (- 7 i)) (range 200)))
(define b4-s (map (lambda (i) (+ i 1)) (range 20)))
(list (dot b4-u b4-v) (shape (outer b4-s b4-s)))
