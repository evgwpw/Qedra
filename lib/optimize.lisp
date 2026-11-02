; optimize.lisp — шаг OPT.1: критические точки и их классификация, множители Лагранжа.
; Только локальная классификация (гессиан/Сильвестр/окаймлённый гессиан);
; глобальный экстремум — не утверждается.
;
; Схема: теорема Ферма (∇f = 0 в точке локального экстремума гладкой f); достаточное условие —
; знакоопределённость гессиана (собственные значения); условная задача — множители Лагранжа
; (∇f = Σλᵢ∇gᵢ при независимых ∇gᵢ), классификация — окаймлённый гессиан (одно ограничение,
; две переменные), иначе — unknown. Сертификат: подстановка (∇f = 0, g = 0) через solve-check
; (символьно; при радикалах — численно), ложная точка — ошибка/#f.

(module optimize
  (export critical-points hessian classify-critical extrema lagrange check-critical opt-real-point? opt-lag-terms
          math-critical-points math-extrema math-hessian math-lagrange))

; ---------- сертификат: подстановка ----------

; ---------- вещественность точек ----------

; точка вещественна: все компоненты — вещественные числа, или выражения без %i,
; которые числятся (eval-num даёт число); root-of без численного значения — не вещественная
; (ограничение: сложную вещественную точку с невычислимым корнем мы отбрасываем —
; лучше недосказать, чем соврать)
(define (opt-real-point? point)
  (and (not (contains-sym? point '%i))
       (every? (lambda (eq)
                  (let ((v (caddr eq)))
                    (or (and (number? v) (not (equal? (type-of v) 'complex)))
                        (let ((n (try (eval-num v) (lambda (err) #f))))
                          (and n (number? n) (not (equal? (type-of n) 'complex)))))))
                point)))

; семейство решений (правая часть зависит от переменных задачи, например ((= x y) (= y y))) —
; не отбрасывать: иначе целая линия критических точек молча теряется
(define (opt-family? point vars)
  (any? (lambda (eq) (any? (lambda (v) (opt-free-sym? (caddr eq) v)) vars)) point))

; вхождение символа вне root-of (там переменная связанная)
(define (opt-free-sym? e v)
  (cond ((equal? e v) #t)
        ((pair? e) (and (not (equal? (car e) 'root-of))
                        (any? (lambda (a) (opt-free-sym? a v)) (cdr e))))
        (else #f)))

; точка — список ((= x a) ...); свернуть все подстановки в выражение (по порядку)
; нормализация n-арного минуса: (- a b c ...) → (- a (+ b c ...)) — форма, которую решает groebner;
; одноэлементную сумму оставляем как есть
(define (opt-norm-minus e)
  (if (and (list? e) (equal? (car e) (quote -)) (> (length e) 3))
      (list (quote -) (cadr e) (opt-sum (cddr e)))
      e))

; сумма списка термов: пусто → 0, один → сам терм, иначе (+ t1 t2 ...)
(define (opt-sum ts)
  (cond ((null? ts) 0)
        ((null? (cdr ts)) (car ts))
        (else (cons (quote +) ts))))

(define (opt-subst point e)
  (if (null? point) e (opt-subst (cdr point) (subst (car point) e))))

; уравнение '(= l r) → выражение (− l r); выражение — как есть
(define (opt-eq->expr eq)
  (if (and (list? eq) (equal? (car eq) '=)) (opt-norm-minus (list '- (cadr eq) (caddr eq))) (opt-norm-minus eq)))

; проверка, что все уравнения (список '= или выражений) обращаются в 0 в точке:
; solve-check → exact | numeric; bad/skip/partial → #f
(define (opt-check-system eqs vars point)
  (let* ((es (map opt-eq->expr eqs))
         (r (solve-check (map (lambda (e) (list '= e 0)) es) vars (list point))))
    (and (or (equal? (car r) 'exact) (equal? (car r) 'numeric)) #t)))

; ---------- критические точки ----------

; (critical-points f vars) → список точек, каждая — ((= x a) ...): решения ∇f = 0.
; f — выражение; vars — список переменных. Сертификат: каждая точка проверяется подстановкой
; (каждая компонента градиента → 0; радикалы — численно внутри solve-check);
; не прошла — ошибка (ложных точек не отдаём).
(define (critical-points f vars)
  (let* ((grad (map (lambda (v) (expand (simplify (diff v f)))) vars))
         (eqs (map (lambda (g) (list '= g 0)) grad))
         (sols (filter (lambda (p) (or (opt-family? p vars) (opt-real-point? p)))
                       (set->list (solve eqs vars)))))
    (map (lambda (p) (if (not (opt-check-system eqs vars p))
                              (error "critical-points: точка не прошла проверку подстановкой" p)))
              sols)
    sols))

; проверка произвольной точки: ложная точка → #f
(define (check-critical f vars point)
  (let* ((grad (map (lambda (v) (expand (simplify (diff v f)))) vars))
         (eqs (map (lambda (g) (list '= g 0)) grad)))
    (opt-check-system eqs vars point)))

; ---------- гессиан ----------

; (hessian f vars) → матрица вторых производных (список списков, как linalg)
(define (hessian f vars)
  (map (lambda (vi)
         (map (lambda (vj) (simplify (diff vi (diff vj f)))) vars))
       vars))

; ---------- классификация ----------

; точка → список значений переменных по порядку vars (отсутствующая переменная → 0)
(define (opt-point-values point vars)
  (map (lambda (v)
         (let ((r (filter (lambda (eq) (equal? (cadr eq) v)) point)))
           (if (null? r) 0 (caddr (car r)))))
       vars))

; знак выражения: символьно (число); иначе численно через eval-num (порог 1e-9);
; не вычислилось — 0 (консервативно: unknown, ложных min/max не отдаём)
(define (opt-sign e)
  (let ((s (simplify e)))
    (cond ((and (number? s) (= s 0)) 0)
          ((number? s) (if (> s 0) 1 -1))
          (else (let ((n (try (eval-num s) (lambda (err) #f))))
                  (cond ((not n) 0)
                        ((> n 1e-9) 1)
                        ((< n -1e-9) -1)
                        (else 0)))))))
; собственные значения матрицы (список списков) → список λ (без кратностей)
(define (opt-eigs m)
  (map car (eigenvalues m)))

; (classify-critical f vars point) → min | max | saddle | unknown.
; Гессиан в точке: все собственные значения > 0 → min; все < 0 → max; есть и те и другие → saddle;
; нулевое (порог 1e-9) → unknown (гессиан вырожден — нужен анализ высших порядков; не min!).
; Одномерный случай — знак f''(x₀).
(define (classify-critical f vars point)
  (let* ((h (hessian f vars))
         (hp (map (lambda (row) (map (lambda (e) (opt-subst point e)) row)) h))
         (eig (if (= (length vars) 1)
                  (list (opt-subst point (car (car hp))))
                  (opt-eigs hp))))
    (cond ((member? 0 (map opt-sign eig)) 'unknown)
          ((every? (lambda (s) (> s 0)) (map opt-sign eig)) 'min)
          ((every? (lambda (s) (< s 0)) (map opt-sign eig)) 'max)
          (else 'saddle))))

; (extrema f vars) → список (точка значение тип) для всех критических точек
(define (extrema f vars)
  (map (lambda (p) (list p (simplify (opt-subst p f)) (classify-critical f vars p)))
       (critical-points f vars)))

; ---------- множители Лагранжа ----------

; (lagrange f constraints vars) → список (точка значение λ-ы тип):
; ограничения — список уравнений g = 0 (форма (= l r) или выражение), vars — переменные задачи.
; Лямбды — свежие символы la1, la2, ...; система: ∂f/∂xⱼ − Σλᵢ·∂gᵢ/∂xⱼ = 0, gᵢ = 0.
; сумма членов Σλᵢ·∂gᵢ/∂v (λ-имя, g) — плоский список термов
(define (opt-lag-terms lam-names gs v)
  (if (null? lam-names)
      0
      (opt-sum (map (lambda (pr) (list (quote *) (car pr) (diff v (cadr pr))))
                            (map2 list lam-names gs)))))

; Классификация: окаймлённый гессиан для одного ограничения и двух переменных, иначе unknown.
; Сертификат: подстановка решения в систему (solve-check); не прошла — ошибка.
(define (lagrange f constraints vars)
  (let* ((gs (map opt-eq->expr constraints))
         (ng (length gs))
         (lam-names (map (lambda (i) (string->symbol (string-append "la" (to-string (+ i 1))))) (range ng)))
         (all-vars (append vars lam-names))
         (lag-eqs (map (lambda (vj)
                        (list (quote -)
                                      (simplify (diff vj f))
                                      (opt-lag-terms lam-names gs vj)))
                      vars))
         (sys (append (map (lambda (e) (list (quote =) e 0)) lag-eqs)
                      (map (lambda (g) (list (quote =) g 0)) gs)))
         (sols (filter opt-real-point? (set->list (solve sys all-vars)))))
    (map (lambda (p) (if (not (opt-check-system sys all-vars p))
                          (error "lagrange: точка не прошла проверку подстановкой" p)))
         sols)
    (map (lambda (p)
           (let* ((val (simplify (opt-subst p f)))
                  (cls (lag-classify f gs vars p lam-names)))
             (list (filter (lambda (eq) (member? (cadr eq) vars)) p) val
                   (filter (lambda (eq) (member? (cadr eq) lam-names)) p) cls)))
         sols)))

; классификация условной точки: окаймлённый гессиан (n = 2, m = 1):
; det [[0, g_x, g_y], [g_x, L_xx, L_xy], [g_y, L_xy, L_yy]], L = f − λg;
; det > 0 → max, det < 0 → min (критерий: знак (−1)^m·det H̃, m = 1);
; det = 0 или другой размер → unknown
(define (lag-classify f gs vars point lam-names)
  (if (not (and (= (length gs) 1) (= (length vars) 2))) 'unknown
      (let* ((g (car gs))
             (lam (if (null? lam-names) 0 (car lam-names)))
             (L (list '- f (list '* lam g)))
             (v1 (car vars)) (v2 (cadr vars))
             (gx (opt-subst point (diff v1 g)))
             (gy (opt-subst point (diff v2 g)))
             (Lxx (opt-subst point (diff v1 (diff v1 L))))
             (Lxy (opt-subst point (diff v1 (diff v2 L))))
             (Lyy (opt-subst point (diff v2 (diff v2 L))))
             (bh (list (list 0 gx gy) (list gx Lxx Lxy) (list gy Lxy Lyy)))
             (s (opt-sign (det bh))))
        (cond ((= s 0) 'unknown)
              ((> s 0) (quote max))
              (else (quote min))))))

; ---------- обёртки для математического языка ----------

; данные из языка: список или tensor → список; переменные — символы
(define (opt-mlang-vars v)
  (let ((l (if (list? v) v (tensor->list (tensor v)))))
    (map (lambda (x) (if (symbol? x) x (string->symbol (to-string x)))) l)))

(define (math-critical-points f vars)
  (critical-points f (opt-mlang-vars vars)))

(define (math-extrema f vars)
  (extrema f (opt-mlang-vars vars)))

(define (math-hessian f vars)
  (tensor (hessian f (opt-mlang-vars vars))))

(define (math-lagrange f constraints vars)
  (lagrange f (if (list? constraints) constraints (tensor->list (tensor constraints)))
            (opt-mlang-vars vars)))

