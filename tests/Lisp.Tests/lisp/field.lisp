; field.lisp — тесты шага FLD.1: один и тот же универсальный код (fp-*, fm-*) над ℚ, ℚ(√2), ℚ(∛2), GF(7), GF(2⁸), ℚ(x).
; Сверка с готовыми реализациями: linalg (rref, nullspace, det, rank), algnum (alg-poly-gcd), gf (gf-poly-gcd, gf-inv).
; Подделки: fp-…-check / fm-…-check должны возвращать #f на испорченном ответе.

(define fq (field-Q))
(define alg2 (alg-field '(+ (^ t 2) -2) 't))        ; ℚ(√2)
(define f2 (field-algnum alg2))
(define alg3 (alg-field '(+ (^ t 3) -2) 't))        ; ℚ(∛2)
(define f3 (field-algnum alg3))
(define f7 (field-gf 7))
(define aes (gf-field 2 '(1 1 0 1 1 0 0 0 1) 't))   ; x⁸+x⁴+x³+x+1
(define f256 (field-gfpn aes))
(define frf (field-ratfun 'x))

(define (flt-transpose m) (map (lambda (j) (map (lambda (r) (nth r j)) m)) (range (length (car m)))))

; ---------- Q: сверка с linalg ----------

(deftest "FLD: ℚ — nullspace/rref/rank/det совпадают с linalg"
  (let ((m '((1 2 3 4) (2 4 6 8) (1 0 1 0))))
    (assert-equal (fm-nullspace fq m) (nullspace m))
    (assert-equal (car (fm-rref fq m)) (tensor->list (rref m)))
    (assert-equal (fm-rank fq m) (rank m)))
  (let ((m '((2 1 0) (1 3 1) (0 1 4))))
    (assert-equal (fm-det fq m) 18)
    (assert-true (= (fm-det fq m) (det m)))))

(deftest "FLD: ℚ — деление с остатком, НОД, Безу"
  (assert-equal (fp-divmod fq '(-1 0 0 1) '(-1 1)) '((1 1 1) ()))
  (assert-equal (fp-divmod fq '(1 0 1) '(1 1)) '((-1 1) (2)))
  (assert-equal (fp-gcd fq '(-1 0 1) '(1 2 1)) '(1 1))
  (let ((e (fp-egcd fq '(-1 0 1) '(1 2 1))))
    (assert-equal (car e) '(1 1))
    (assert-true (fp-egcd-check fq '(-1 0 1) '(1 2 1) e)))
  (assert-equal (fp-deriv fq '(5 4 3 2 1)) '(4 6 6 4))
  (assert-equal (fp-eval fq '(1 2 3) 2) 17)
  (assert-equal (fp-compose fq '(0 0 1) '(1 1)) '(1 2 1)))

(deftest "FLD: ℚ — бесквадратное разложение (Yun)"
  ; 3·(x−1)·(x+1)²·(x²+1)³
  (let* ((a '(-1 1)) (b '(1 1)) (c '(1 0 1))
         (f (fp-scale fq 3 (fp-mul fq a (fp-mul fq (fp-mul fq b b) (fp-mul fq c (fp-mul fq c c))))))
         (r (fp-sqfree fq f)))
    (assert-equal r (list 3 (list (list a 1) (list b 2) (list c 3))))
    (assert-true (fp-sqfree-check fq f r))))

; ---------- ℚ(√2) ----------

(deftest "FLD: ℚ(√2) — gcd(x²−2, x²+2√2x+2) = x+√2, сверка с alg-poly-gcd"
  (let ((a '((-2) () (1))) (b '((2) (0 2) (1))))
    (assert-equal (fp-gcd f2 a b) '((0 1) (1)))
    (assert-equal (fp-gcd f2 a b) (alg-poly-gcd alg2 a b))
    (assert-true (fp-gcd-check f2 a b '((0 1) (1))))
    (assert-equal (fp-gcd fq '(-2 0 1) '(2 0 1)) '(1))))

(deftest "FLD: ℚ(√2) — ядро матрицы, вырожденной только над ℚ(√2)"
  (let ((m '(((1) (0 1)) ((0 1) (2)))))
    (assert-equal (fm-rank f2 m) 1)
    (assert-equal (fm-nullspace f2 m) '(((0 -1) (1))))
    (assert-equal (fm-det f2 m) '())
    (assert-equal (fm-inverse f2 m) #f)))

(deftest "FLD: ℚ(√2) — обратная матрица и решение системы"
  (let* ((m '(((1) (0 1)) ((0 1) (3))))
         (inv (fm-inverse f2 m)))
    (assert-equal inv '(((3) (0 -1)) ((0 -1) (1))))
    (assert-true (fm-inverse-check f2 m inv))
    (let ((s (fm-solve f2 m '((1) (0 1)))))
      (assert-equal (cadr s) '())
      (assert-equal (fm-mat-vec f2 m (car s)) '((1) (0 1))))))

(deftest "FLD: ℚ(√2) — sqfree (x−√2)²"
  (let* ((a '((0 -1) (1))) (f (fp-mul f2 a a)) (r (fp-sqfree f2 f)))
    (assert-equal r (list '(1) (list (list a 2))))))

; ---------- ℚ(∛2) ----------

(deftest "FLD: ℚ(∛2) — ядро [[1,a],[a²,2]], gcd и det"
  (let ((m '(((1) (0 1)) ((0 0 1) (2)))))
    (assert-equal (fm-rank f3 m) 1)
    (assert-equal (length (fm-nullspace f3 m)) 1)
    (assert-equal (fm-rank fq '((1 0) (0 0))) 1))
  (assert-equal (fp-gcd f3 '((-2) () () (1)) '((0 -1) (1))) '((0 -1) (1)))
  (let ((m '(((1) (0 1) (0 0 1)) ((0 1) (0 0 1) (2)) ((1) (1) (1)))))
    (assert-true (field-equal? f3 (fm-det f3 m) (fm-det f3 (flt-transpose m))))))

; ---------- GF(7) ----------

(deftest "FLD: GF(7) — НОД как в gf-poly-gcd, обратная матрица"
  (let ((a '(6 5 1)) (b '(1 1)))
    (assert-equal (fp-gcd f7 a b) (gf-poly-gcd a b 7)))
  (let ((a '(3 0 1 4)) (b '(1 5 2)))
    (assert-equal (fp-gcd f7 a b) (gf-poly-gcd a b 7))
    (assert-true (fp-gcd-check f7 a b (gf-poly-gcd a b 7))))
  (let* ((m '((1 2) (3 4))) (inv (fm-inverse f7 m)))
    (assert-true (fm-inverse-check f7 m inv))
    (assert-equal (fm-mul f7 m inv) '((1 0) (0 1))))
  (assert-equal (fm-det f7 '((1 2) (3 4))) 5)
  (assert-equal (field-from-rational f7 1/2) 4)
  (assert-error (field-from-rational f7 1/7)))

(deftest "FLD: GF(7) — sqfree с седьмой степенью: (x+1)⁷(x+2)²(x²+1)"
  (let* ((a '(1 1)) (b '(2 1)) (c '(1 0 1))
         (a7 (fp-mul f7 (fp-mul f7 (fp-mul f7 a a) (fp-mul f7 a a)) (fp-mul f7 (fp-mul f7 a a) a)))
         (f (fp-mul f7 a7 (fp-mul f7 (fp-mul f7 b b) c)))
         (r (fp-sqfree f7 f)))
    (assert-equal a7 '(1 0 0 0 0 0 0 1))
    (assert-equal r (list 1 (list (list c 1) (list b 2) (list a 7))))
    (assert-true (fp-sqfree-check f7 f r))))

(deftest "FLD: GF(7) — линейная система с ядром"
  (let* ((m '((1 2 3) (2 4 6))) (s (fm-solve f7 m '(1 2))))
    (assert-equal (length (cadr s)) 2)
    (assert-equal (fm-solve f7 m '(1 3)) #f)))

; ---------- GF(2⁸) ----------

(deftest "FLD: GF(2⁸) — обратный как gf-inv ({53}⁻¹ = {CA}), матрица"
  (let ((x (gf-elt aes 83)))
    (assert-equal (field-inv f256 x) (gf-inv aes x))
    (assert-equal (gf->int aes (field-inv f256 x)) 202)
    (assert-equal (field-mul f256 x (field-inv f256 x)) '(1)))
  (let* ((m (list (list (gf-elt aes 2) (gf-elt aes 3)) (list '(1) (gf-elt aes 7))))
         (inv (fm-inverse f256 m)))
    (assert-true (fm-inverse-check f256 m inv))
    (assert-equal (fm-mul f256 m inv) (fm-identity f256 2))))

(deftest "FLD: GF(2⁸) — sqfree квадрата (x+a)²: корень p-й степени в поле"
  (let* ((a (gf-elt aes 5)) (l (list a '(1))) (f (fp-mul f256 l l)) (r (fp-sqfree f256 f)))
    (assert-equal r (list '(1) (list (list l 2))))
    (assert-true (fp-sqfree-check f256 f r))))

(deftest "FLD: GF(2⁸) — НОД и Безу"
  (let* ((a (gf-elt aes 5)) (l (list a '(1)))
         (f (fp-mul f256 l (list '(1) '(1))))
         (g (fp-mul f256 l (list '(0 1) '(1)))))
    (assert-equal (fp-gcd f256 f g) l)
    (assert-true (fp-egcd-check f256 f g (fp-egcd f256 f g)))))

; ---------- ℚ(x) ----------

(deftest "FLD: ℚ(x) — обратная, ранг, НОД"
  (assert-equal (field-from-rational frf 1/2) 1/2)
  (assert-true (field-zero? frf (field-sub frf (field-inv frf '(+ x 1)) (field-inv frf '(+ 1 x)))))
  (assert-equal (fm-rank frf (list (list 1 'x) (list 'x '(^ x 2)))) 1)
  (assert-equal (length (fp-gcd frf (list '(* -1 (^ x 2)) 0 1) (list '(* -1 x) 1))) 2))

; ---------- подделки сертификатов ----------

(deftest "FLD: подделка ядра отвергается"
  (let* ((m '(((1) (0 1)) ((0 1) (2)))) (v (car (fm-nullspace f2 m))))
    (assert-true (fm-nullspace-check f2 m (list v)))
    (assert-equal (fm-nullspace-check f2 m (list (list '(1) '(1)))) #f)
    (assert-equal (fm-nullspace-check f2 m (list (list '() '()))) #f)
    (assert-equal (fm-nullspace-check f2 m '()) #f)
    (assert-equal (fm-nullspace-check f2 m (list v v)) #f))
  (assert-equal (fm-nullspace-check fq '((1 2) (3 4)) (list '(2 -1))) #f))

(deftest "FLD: подделка НОД и Безу отвергается"
  (let ((a '((-2) () (1))) (b '((2) (0 2) (1))))
    (assert-equal (fp-gcd-check f2 a b '((1))) #f)
    (assert-equal (fp-gcd-check f2 a b '((0 2) (2))) #f)
    (assert-equal (fp-gcd-check f2 a b '((0 -1) (1))) #f)
    (assert-equal (fp-gcd-check f2 a b a) #f)
    (assert-equal (fp-egcd-check f2 a b (list '((0 1) (1)) '((1)) '((1)))) #f)
    (assert-equal (fp-egcd-check fq '(-1 0 1) '(1 2 1) (list '(1 1) '(1) '(1))) #f))
  (assert-equal (fp-gcd-check f7 '(6 5 1) '(2 1) '(1)) #f)
  (assert-true (fp-gcd-check f7 '(6 5 1) '(2 1) '(2 1))))

(deftest "FLD: подделка обратной, решения, деления, sqfree отвергается"
  (let* ((m '(((1) (0 1)) ((0 1) (3)))) (inv (fm-inverse f2 m)))
    (assert-equal (fm-inverse-check f2 m '(((3) (0 -1)) ((0 -1) (2)))) #f)
    (assert-equal (fm-inverse-check f2 m m) #f)
    (assert-equal (fm-inverse-check f2 m #f) #f)
    (assert-true (fm-inverse-check f2 m inv)))
  (assert-equal (fm-solve-check fq '((1 2) (2 4)) '(1 2) (list '(0 0) '((-2 1)))) #f)
  (assert-equal (fm-solve-check fq '((1 2) (2 4)) '(1 2) (list '(1 0) '((1 1)))) #f)
  (assert-true (fm-solve-check fq '((1 2) (2 4)) '(1 2) (list '(1 0) '((-2 1)))))
  (assert-equal (fp-divmod-check fq '(1 0 1) '(1 1) '(-1 1) '(3)) #f)
  (assert-equal (fp-divmod-check fq '(1 0 1) '(1 1) '(0 1) '(1 0 1)) #f)
  (let ((f '(-1 0 1)))
    (assert-equal (fp-sqfree-check fq f (list 1 (list (list '(-1 1) 2)))) #f)
    (assert-equal (fp-sqfree-check fq f (list 1 (list (list f 1)))) #t)
    (assert-equal (fp-sqfree-check fq f (list 1 (list (list '(-1 1) 1) (list '(1 1) 1)))) #f)   ; кратности должны быть различны
    (assert-equal (fp-sqfree-check fq f (list 1 (list (list '(-1 1) 1) (list '(1 1) 2)))) #f)
    (assert-equal (fp-sqfree-check fq '(1 2 1) (list 1 (list (list '(1 1) 1) (list '(1 1) 1)))) #f)
    (assert-equal (fp-sqfree-check fq '(0 0 1) (list 1 (list (list '(0 1) 2)))) #t)))

; ---------- вырожденные случаи ----------

(deftest "FLD: вырожденные случаи"
  (assert-equal (fm-nullspace fq '((0 0) (0 0))) '((1 0) (0 1)))
  (assert-equal (fm-rank fq '((0 0) (0 0))) 0)
  (assert-equal (fm-nullspace fq '()) '())
  (assert-equal (fm-rank fq '()) 0)
  (assert-equal (fm-det fq '()) 1)
  (assert-equal (fm-inverse fq '()) '())
  (assert-equal (fm-det fq '((5))) 5)
  (assert-equal (fm-inverse fq '((4))) '((1/4)))
  (assert-equal (fm-inverse fq '((0))) #f)
  (assert-equal (fm-inverse fq '((1 2) (2 4))) #f)
  (assert-equal (fm-solve fq '((0 0)) '(1)) #f)
  (assert-equal (fm-solve fq '((0 0)) '(0)) '((0 0) ((1 0) (0 1))))
  (assert-equal (fp-gcd fq '() '()) '())
  (assert-equal (fp-gcd fq '() '(2 2)) '(1 1))
  (assert-equal (fp-gcd fq '(5) '(1 1)) '(1))
  (assert-equal (fp-divmod fq '() '(1 1)) '(() ()))
  (assert-equal (fp-divmod fq '(1) '(1 1)) '(() (1)))
  (assert-equal (fp-mul fq '() '(1 1)) '())
  (assert-equal (fp-sqfree fq '()) '(0 ()))
  (assert-equal (fp-sqfree fq '(7)) '(7 ()))
  (assert-equal (fp-deriv fq '(3)) '())
  (assert-equal (fp-trim fq '(1 0 0)) '(1))
  (assert-error (fp-divmod fq '(1 1) '()))
  (assert-error (field-inv fq 0))
  (assert-error (field-inv f2 '()))
  (assert-error (field-inv f7 0))
  (assert-error (field-inv f256 '()))
  (assert-error (field-inv frf 0))
  (assert-error (fm-det fq '((1 2))))
  (assert-error (fm-inverse fq '((1 2))))
  (assert-equal (field-name fq) "Q")
  (assert-equal (field-char f7) 7)
  (assert-equal (field->expr f256 '(1 1)) '(+ 1 t)))
