; Линейная алгебра (lib/linalg.lisp): ядро, собственные значения, жорданова форма, матричная экспонента.
(define A '((2 1) (0 2)))     ; жорданова клетка: недиагонализуемая
(define B '((1 2) (2 1)))

(display "rref B: ") (display (rref B)) (newline)
(display "charpoly B: ") (display (charpoly B 'l)) (newline)
(display "eigenvalues B: ") (display (eigenvalues B)) (newline)
(display "eigenvectors B: ") (display (eigenvectors B)) (newline)
(display "nullspace [[1 2][2 4]]: ") (display (nullspace '((1 2) (2 4)))) (newline)

(display "diagonalizable? B: ") (display (diagonalizable? B)) (newline)
(display "diagonalizable? A: ") (display (diagonalizable? A)) (newline)

(define pj (jordan-form A))
(display "jordan-form A: ") (display pj) (newline)

(display "mat-exp A t: ") (display (mat-exp A 't)) (newline)
(display "mat-power B n=5: ") (display (mat-power B 5)) (newline)
