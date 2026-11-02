; poly.lisp — тонкие обёртки над многочленными builtins шага 17 (together, cancel, apart, factor,
; poly-gcd, coeff, degree и т.д. — на F#). Здесь только удобства, не требующие скорости.

(module poly
  (export coefficients leading-coefficient coefficients->poly poly-divides?))

; (coefficients e x) — список коэффициентов (c0 c1 ... cn) многочлена e по x; нулевой многочлен → ()
(define (coefficients e x)
  (let ((d (degree e x)))
    (if (integer? d)
        (map (lambda (k) (coeff e x k)) (range (+ d 1)))
        '())))

; (leading-coefficient e x) — старший коэффициент по x (0 для нулевого многочлена)
(define (leading-coefficient e x)
  (let ((d (degree e x)))
    (if (integer? d) (coeff e x d) 0)))

; (coefficients->poly (c0 c1 ... cn) x) — многочлен в канонической форме
(define (coefficients->poly cs x)
  (simplify (cons '+ (map2 (lambda (c k) (list '* c (list '^ x k))) cs (range (length cs))))))

; (poly-divides? a b x) — a делит b нацело (многочлены): остаток по x равен нулю в каноническом виде
(define (poly-divides? a b x)
  (equal? (poly-remainder b a x) 0))
