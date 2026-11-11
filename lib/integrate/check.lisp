; integrate/check.lisp — проверка первообразной дифференцированием и вспомогательные численные функции (часть бывшего
; lib\integrate.lisp, шаг 21h'). Загружается после integrate/parts.lisp.
; int-check — документированный API; int-num используют limit и api.lisp
(module integrate
  (export int-check int-check-how int-num))

; ---------- проверка дифференцированием ----------

; точки и параметры — рациональные числа (Шаг 21h): суммы по корням (root-sum) в производной eval-num считает ТОЧНО в ℚ[t]/(Q),
; небольшие знаменатели (3/10, а не двоичная дробь 0.3) удерживают размер чисел в этой арифметике
(define int-test-points '(3/10 47/100 71/100 137/100 11/5))
(define int-test-params '(17/10 23/10 19/10 31/10 13/10 29/10 11/10 27/10))

; символы-параметры выражения (не головы функций, не x, не константы pi и %i)
(define (int-symbols e x)
  (cond ((and (symbol? e) (not (equal? e x)) (not (member? e '(pi %i)))) (list e))
        ; (root-sum t Q E): связанная переменная t — не параметр
        ((and (op-expr? e) (equal? (car e) 'root-sum) (= (length e) 4))
         (filter (lambda (s) (not (equal? s (cadr e))))
                 (int-dedupe (append (int-symbols (nth e 2) x) (int-symbols (nth e 3) x)))))
        ((op-expr? e) (int-dedupe (append-map (lambda (a) (int-symbols a x)) (cdr e))))
        (else '())))

; гиперболические функции — через exp/log (eval-num их не вычисляет)
(define (int-hyp e)
  (if (op-expr? e)
      (let ((args (map int-hyp (cdr e))) (h (car e)))
        (let ((u (if (null? args) #f (car args))))
          (cond ((equal? h 'sinh) (list '* 1/2 (list '+ (list 'exp u) (list '* -1 (list 'exp (list '* -1 u))))))
                ((equal? h 'cosh) (list '* 1/2 (list '+ (list 'exp u) (list 'exp (list '* -1 u)))))
                ((equal? h 'tanh) (let ((p (list 'exp u)) (m (list 'exp (list '* -1 u))))
                                    (list '* (list '+ p (list '* -1 m)) (list '^ (list '+ p m) -1))))
                ((equal? h 'sech) (list '* 2 (list '^ (list '+ (list 'exp u) (list 'exp (list '* -1 u))) -1)))
                ((equal? h 'csch) (list '* 2 (list '^ (list '+ (list 'exp u) (list '* -1 (list 'exp (list '* -1 u)))) -1)))
                ((equal? h 'coth) (let ((p (list 'exp u)) (m (list 'exp (list '* -1 u))))
                                    (list '* (list '+ p m) (list '^ (list '+ p (list '* -1 m)) -1))))
                ((equal? h 'asinh) (list 'log (list '+ u (list '^ (list '+ (list '^ u 2) 1) 1/2))))
                ((equal? h 'atanh) (list '* 1/2 (list 'log (list '* (list '+ 1 u) (list '^ (list '+ 1 (list '* -1 u)) -1)))))
                (else (cons h args)))))
      e))

; |значение| выражения в точке (x = p, параметры — фиксированные числа) или #f
(define (int-abs-at d x p vals)
  (try (num-abs (eval-num (int-hyp (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr)))
                                          (replace-expr d x p) vals))))
       (lambda (err) #f)))

; tol — допуск невязки относительно 1 + |e|; pts — точки.
; Состояние: 'ok (невязка мала во всех вычислимых точках, их не меньше двух), 'bad (где-то велика),
; 'skip (вычислимых точек меньше двух — проверить нечем)
(define (int-numeric-status-at dfe e x tol pts)
  (let* ((ps (int-symbols (list '+ dfe e) x))
         (vals (map2 list ps int-test-params))
         ; по каждой точке: 'skip (не вычислилось), #t (невязка мала) или #f
         (rs (filter (lambda (r) (not (equal? r 'skip)))
                     (map (lambda (p)
                            (let ((a (int-abs-at dfe x p vals)) (b (int-abs-at e x p vals)))
                              (if (and a b) (< a (* tol (+ 1 b))) 'skip)))
                          pts))))
    (cond ((< (length rs) 2) 'skip)
          ((every? (lambda (r) r) rs) 'ok)
          (else 'bad))))

; Шаг INT.BR: вещественное ли значение (допускается мнимый шум дробных степеней)
(define (int-real-val? v)
  (cond ((real-numeric? v) #t)
        ((and (op-expr? v) (equal? (car v) '+) (= (length v) 3) (real-numeric? (nth v 1))
              (op-expr? (nth v 2)) (equal? (car (nth v 2)) '*) (= (length (nth v 2)) 3)
              (equal? (nth (nth v 2) 2) '%i) (real-numeric? (nth (nth v 2) 1)))
         (< (abs (nth (nth v 2) 1)) 0.000000001))
        (else #f)))

; точки x < 0, где e определено и вещественно (при параметрах — пробные числа); #t, если таких не меньше двух
(define int-neg-test-points '(-3/10 -47/100 -71/100 -137/100 -11/5))
(define (int-real-on-neg? e x) (int-real-on-neg-all? (list e) x int-neg-test-points))

; ближайшие к нулю точки: проверка int-check только в них (дальше за корнем радикала главные значения √u·√v и √(u·v)
; расходятся знаком, хотя ответ на своём интервале верен)
(define int-neg-near-points '(-3/10 -47/100))

; то же для списка выражений: в точке вещественны ВСЕ (иначе ветви главных значений не обязаны сходиться);
; pts — точки, нужны хотя бы две вещественные (для двух точек — обе)
(define (int-real-on-neg-all? es x pts)
  (let* ((ps (int-dedupe (append-map (lambda (e) (int-symbols e x)) es)))
         (vals (map2 list ps int-test-params))
         (n (length (filter (lambda (p)
                              (every? (lambda (e)
                                        (try (int-real-val? (eval-num (int-hyp (foldl (lambda (acc pr) (replace-expr acc (car pr) (cadr pr)))
                                                                                     (replace-expr e x p) vals))))
                                             (lambda (err) #f)))
                                      es))
                            pts))))
    (>= n 2)))

(define (int-numeric-zero-at? dfe e x tol pts) (equal? (int-numeric-status-at dfe e x tol pts) 'ok))

(define (int-numeric-zero? dfe e x) (int-numeric-zero-at? dfe e x 0.0000001 int-test-points))

; (int-check-how F e x) → чем доказано d/dx F = e: 'simplify | 'together (точно), 'numeric (в пробных точках),
; иначе 'bad (численно не сходится) или 'skip (численно проверить нечем). Шаг 22.6: сертификат derivative
(define (int-check-how F e0 x)
  (let ((diffed (int-diff x F)) (e (simplify e0)))
    (let ((dfe (list '- diffed e)))
      (cond ((equal? (simplify dfe) 0) 'simplify)
            ((equal? (try (together dfe) (lambda (err) #f)) 0) 'together)
            (else (let ((st (int-numeric-status-at dfe e x 0.0000001 int-test-points)))
                    ; Шаг INT.BR: точки только x > 0 пропускали ответы, неверные при x < 0 (√(1−x²) = |x|·√(x⁻²−1));
                    ; где подынтегральное вещественно и при x < 0 — проверяем и там
                    (if (equal? st 'ok)
                        (if (and (int-real-on-neg-all? (list e F) x int-neg-near-points)
                                 (equal? (int-numeric-status-at dfe e x 0.0000001 int-neg-near-points) 'bad))
                            'bad
                            'numeric)
                        st)))))))

; (int-check F e x) → #t, если d/dx F = e: точно (simplify, together) либо численно
(define (int-check F e0 x)
  (let ((how (int-check-how F e0 x)))
    (or (equal? how 'simplify) (equal? how 'together) (equal? how 'numeric))))

; (Шаг 21c: значения функций в точке — sin(π/2), exp(0), atan(1), 0^p, ... — считает сам simplify;
;  прежний обход int-fold / int-fold-call удалён)

; логарифм неположительного числа (особенность или ветвь) — определённый интеграл не вычисляем
(define (int-bad-log? e)
  (cond ((and (op-expr? e) (equal? (car e) 'log) (= (length e) 2) (real-numeric? (cadr e)) (<= (cadr e) 0)) #t)
        ((op-expr? e) (any? int-bad-log? (cdr e)))
        (else #f)))

; числовое значение предела (число, либо вычисляемое выражение вроде (exp 1)) или #f (символ)
(define (int-num v)
  (if (real-numeric? v)
      v
      (let ((n (try (eval-num v) (lambda (err) #f))))
        (if (and n (real-numeric? n)) n #f))))

; вещественный корень знаменателя в [a, b] (для символьных пределов — любой вещественный корень)
(define (int-singular? e x a b)
  (let ((den (try (denom e) (lambda (err) 1))) (na (int-num a)) (nb (int-num b)))
    (and (not (x-free? den x))
         (numeric-poly? den x)
         (any? (lambda (r) (or (not (and na nb))
                               (and (<= na r) (<= r nb))))
               (real-roots den x)))))
