; hurwitz.lisp — дзета Гурвица ζ(s, a) = Σ_{k≥0} (k + a)^(−s) (шаг ZETA.HURWITZ)
;
; Голова выражения — (zeta s a) (двуарная; одноарная (zeta s) — дзета Римана, как раньше).
;   производная по a:   d/da ζ(s, a) = −s·ζ(s+1, a)   (F#: Differentiate.fs, цепное правило по x);
;   численно:           eval-num считает (zeta s a) для вещественных s ≠ 1, a > 0 (Эйлер — Маклорен, N = 30, 8 членов;
;                       |s| ≤ 60) и для a < 0 не целого при целом s (сдвиг вверх ζ(s, a) = a^(−s) + ζ(s, a+1));
;   связь с полигаммой: ψ^(n)(a) = (−1)^(n+1)·n!·ζ(n+1, a),  ζ(n, a) = (−1)^n·ψ^(n−1)(a)/(n−1)!  (n ≥ 1 целое).
; Здесь — только переписывание голов; интеграл ∫ x^m·ζ(s, a+bx) — lib/integrate/hurwitz.lisp.
(module hurwitz
  (export hz-zeta-num hz-psi->zeta hz-zeta->psi))

(define (hz-fact n) (let loop ((i 2) (acc 1)) (if (> i n) acc (loop (+ i 1) (* acc i)))))

; число (double) или #f: ζ(s, a) от чисел (хотя бы одно float) через eval-num
(define (hz-zeta-num s a)
  (let ((r (try (eval-num (list 'zeta s a)) (lambda (er) #f))))
    (and r (number? r) (equal? (type-of r) 'float) (= r r) r)))

; (psi u n) и (poly_gamma n u) при целом n ≥ 1 → (−1)^(n+1)·n!·ζ(n+1, u); остальное без изменений
(define (hz-psi->zeta e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'psi) (= (length e) 3) (integer? (caddr e)) (>= (caddr e) 1))
         (* (^ -1 (+ (caddr e) 1)) (hz-fact (caddr e)) (list 'zeta (+ (caddr e) 1) (hz-psi->zeta (cadr e)))))
        ((and (equal? (car e) 'poly_gamma) (= (length e) 3) (integer? (cadr e)) (>= (cadr e) 1))
         (* (^ -1 (+ (cadr e) 1)) (hz-fact (cadr e)) (list 'zeta (+ (cadr e) 1) (hz-psi->zeta (caddr e)))))
        (else (cons (car e) (map hz-psi->zeta (cdr e))))))

; (zeta n u) при целом n ≥ 2 → (−1)^n·ψ(u, n−1)/(n−1)!; одноарная zeta и нечисловые порядки без изменений
(define (hz-zeta->psi e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'zeta) (= (length e) 3) (integer? (cadr e)) (>= (cadr e) 2))
         (/ (* (^ -1 (cadr e)) (list 'psi (hz-zeta->psi (caddr e)) (- (cadr e) 1))) (hz-fact (- (cadr e) 1))))
        (else (cons (car e) (map hz-zeta->psi (cdr e))))))
