; Lisp-тесты тензора (lib\tensor.lisp), Шаг 15b

(deftest "конструкторы: вектор и матрица"
  (assert-equal (shape (tensor '(1 2 3))) '(3))
  (assert-equal (shape (tensor '((1 2 3) (4 5 6)))) '(2 3))
  (assert-equal (tensor->list (identity-matrix 2)) '((1 0) (0 1))))

(deftest "make-tensor и tensor-from-flat"
  (assert-equal (tensor->list (make-tensor '(2 2) (lambda (i) (+ (car i) (cadr i))))) '((0 1) (1 2)))
  (assert-equal (tensor->list (tensor-from-flat '(2 2) '(a b c d))) '((a b) (c d))))

(deftest "сложение тензоров"
  (assert-equal (tensor->list (+ (tensor '(1 2)) (tensor '(10 20)))) '(11 22))
  (assert-equal (tensor->list (simplify (+ (tensor '(a 1)) (tensor '(a 1))))) '((* 2 a) 2)))

(deftest "скаляр на тензор"
  (assert-equal (tensor->list (* 3 (tensor '(1 2)))) '(3 6))
  (assert-equal (tensor->list (scale 2 '((1 2) (3 4)))) '((2 4) (6 8))))

(deftest "скаляр-выражение (+ a b) — не тензор"
  (assert-equal (tensor->list (simplify (* (+ 'a 'b) (tensor '(1 2)))))
                '((+ a b) (* 2 (+ a b))))
  (assert-equal (tensor->list (scale (+ 'a 'b) '(1 2))) (tensor->list (simplify (* (+ 'a 'b) (tensor '(1 2)))))))

(deftest "Dot: матрица на вектор"
  (assert-equal (tensor->list (* (tensor '((1 2) (3 4))) (tensor '(1 1)))) '(3 7))
  (assert-equal (dot '(1 2 3) '(4 5 6)) 32))

(deftest "матрица в степени -1 и 2"
  (assert-equal (tensor->list (^ (tensor '((1 2) (3 4))) -1)) '((-2 1) (3/2 -1/2)))
  (assert-equal (tensor->list (^ (tensor '((1 1) (0 1))) 2)) '((1 2) (0 1))))

(deftest "det"
  (assert-equal (det '((1 2) (3 4))) -2)
  (assert-equal (det '((2 0 0) (0 3 0) (0 0 4))) 24))

(deftest "diff покомпонентно"
  (assert-equal (tensor->list (diff 'x (tensor '((^ x 2) (* 3 x))))) '((* 2 x) 3)))

(deftest "rank и transpose"
  (assert-equal (rank '((1 2) (2 4))) 1)
  (assert-equal (tensor->list (mat-t '((1 2) (3 4)))) '((1 3) (2 4))))

(deftest "ошибки форм"
  (assert-error (tensor '((1 2) (3))))
  (assert-error (tensor '()))
  (assert-error (+ (tensor '(1 2)) (tensor '(1 2 3))))
  (assert-error (det '((1 2 3) (4 5 6))))
  (assert-error (tref (tensor '(1 2)) 5))
  (assert-error (inv '((1 2) (2 4)))))
