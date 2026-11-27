; zerotest.lisp — общий тест «выражение тождественно равно нулю?» (шаг CHECK.DUAL).
;
; До шага вопрос решался в трёх местах по-разному: Риш (rs-zero?, together + точная подстановка для (сумма)^n, n > 32),
; проверка первообразной (int-check: simplify/together + численно) и оракул стенда (exactDiff: подстановка рациональной точки +
; simplify/expand). Здесь — один ответ 'zero | 'nonzero | 'unknown и одно правило честности: 'zero не выдаётся без подтверждения
; во ВСЕХ точках; подстановка не удалась (полюс, не число) — 'unknown, а не догадка.
;
; (zero-test e vars [опции…]) → 'zero | 'nonzero | 'unknown
;   vars — символы, вместо которых подставляются целые точки; #f — все символы e (кроме pi, %i); () — ни одного.
;   Порядок: (1) дёшево — together даёт 0 → 'zero, ненулевое рациональное число → 'nonzero (опция 'points-only пропускает этот шаг:
;   вызывающий уже вычислил together); (2) точная подстановка нескольких (по умолчанию 3) разных целых точек вместо vars и
;   рациональная арифметика: ровно 0 во всех точках → 'zero; ненулевое число хотя бы в одной → 'nonzero; иначе (полюс, остался
;   не число) → 'unknown. Остаток — замкнутая константа (log 2, √3, π): решает const-zero? (точно; unknown — не решено).
;   Опции: 'zero-only — вызывающему нужно лишь «нуль или нет»: ответ 'zero | 'unknown, точки идут по очереди и счёт кончается на первой
;   ненулевой или невычислимой; 'kernels — перед подстановкой log рациональных заменяются независимыми целыми (как делал Риш для степеней суммы:
;   (1 + θ)^300 с log 2 внутри иначе не вычисляется); тогда 'zero верно (нуль при независимых значениях ядер — нуль
;   многочлена от них), а 'nonzero означает лишь «нуль не подтверждён» (log 6 − log 2 − log 3 ядра-независимо ≠ 0);
;   (points n) — число точек; (time с) — бюджет подбора точек (по умолчанию 2 с; истёк — 'unknown); (at правила) — одна заданная точка: правила subst (список (символ значение)), без together и без
;   подбора точек — решение в оракуле стенда: simplify, при остатке simplify(expand), затем const-zero?.
;   'zero по точкам — подтверждение в n точках, а не доказательство тождества (оно — together = 0); для дробей степени
;   больше n число точек надо увеличить.
(module zerotest
  (export zero-test))

(define (zt-opt? opts k) (member? k opts))
(define (zt-opt-val opts k d)
  (let ((p (filter (lambda (o) (and (pair? o) (equal? (car o) k))) opts)))
    (if (null? p) d (cadr (car p)))))

(define (zt-uniq l) (foldl (lambda (acc a) (if (member? a acc) acc (append acc (list a)))) '() l))
(define (zt-index-of a l) (let loop ((l l) (i 0)) (cond ((null? l) 0) ((equal? (car l) a) i) (else (loop (cdr l) (+ i 1))))))
(define (zt-size e) (if (pair? e) (+ 1 (foldl (lambda (a x) (+ a (zt-size x))) 0 e)) 1))
(define (zt-log-consts e)
  (cond ((not (pair? e)) '())
        ((and (equal? (car e) 'log) (= (length e) 2) (rational-number? (cadr e))) (list e))
        (else (append-map zt-log-consts (cdr e)))))

; значение после подстановки: рациональное число | 0/1 (константа: 0 — доказанный нуль, 1 — доказанный не-нуль) | 'fail
; 0 в неположительной степени (полюс): const-zero? и simplify такие остатки «обнуляют» (0·∞ → 0), доверять им нельзя
(define (zt-zero-pow? r)
  (and (pair? r)
       (or (and (equal? (car r) '^) (= (length r) 3) (equal? (cadr r) 0) (not (and (rational-number? (caddr r)) (> (caddr r) 0))))
           (any? zt-zero-pow? (cdr r)))))
; замкнутая константа численно заметно не нуль: |значение| > 1e-6 (double, ошибка порядка 1e-13) — не нуль и без const-zero?,
; которая на остатках вида cos(…)^(5/2) съедает весь бюджет подбора точек; комплексное значение eval-num — (+ re (* im %i))
(define (zt-num-big? r)
  (let ((v (try (eval-num r) (lambda (e) #f))))
    (cond ((real-numeric? v) (> (abs v) 0.000001))
          ((and (pair? v) (equal? (car v) '+) (= (length v) 3) (real-numeric? (nth v 1))
                (pair? (nth v 2)) (equal? (car (nth v 2)) '*) (= (length (nth v 2)) 3)
                (real-numeric? (nth (nth v 2) 1)) (equal? (nth (nth v 2) 2) '%i))
           (> (+ (abs (nth v 1)) (abs (nth (nth v 2) 1))) 0.000001))
          (else #f))))
; fast? — только для 'zero-only: там «не нуль» значит лишь «не подтверждён», и численная отсечка ложного 'zero не даёт;
; в остальных режимах 'nonzero решает (Риш: «неэлементарно»), а double при сокращении больших слагаемых может ошибиться
(define (zt-value r &rest fast)
  (cond ((zt-zero-pow? r) 'fail)
        ((rational-number? r) r)
        ((and (pair? r) (null? (const-free-syms r)) (<= (zt-size r) 300) (const-closed? r))
         (if (and (pair? fast) (car fast) (zt-num-big? r))
             1
             (let ((z (const-zero? r))) (cond ((equal? z #t) 0) ((equal? z #f) 1) (else 'fail)))))
        (else 'fail)))

; значение выражения в k-й пробной точке (как rs-num-eval Риша: те же числа)
; fast? ('zero-only): остаток после подстановки, который eval-num не вычисляет в число (asin вне [−1, 1], вложенные корни от
; отрицательных, полюс), не доказывает нуль и const-zero? — только 'fail; без этого const-zero?/together на таком остатке
; (≈ 50 мс на точку, сотни знаков) шли в поиске Rubi на каждом кандидате
(define (zt-evaluable? s)
  (or (rational-number? s)
      (let ((v (try (eval-num s) (lambda (e) #f))))
        (or (real-numeric? v)
            (and (pair? v) (equal? (car v) '+) (= (length v) 3) (real-numeric? (nth v 1))
                 (pair? (nth v 2)) (equal? (car (nth v 2)) '*) (= (length (nth v 2)) 3)
                 (real-numeric? (nth (nth v 2) 1)) (equal? (nth (nth v 2) 2) '%i))))))
(define (zt-point e vars k kernels? &rest more)
  (try (let* ((lcs (if kernels? (zt-uniq (zt-log-consts e)) '()))
              (e1 (foldl (lambda (acc lc) (replace-expr acc lc (+ 3 (modulo (+ 41 (* 13 k) (* 7 (zt-index-of lc lcs))) 31))))
                         e lcs))
              (vs (cond ((pair? vars) vars)
                        ((null? vars) '())
                        ; variables отдаёт и ядра ((1 + θ)^299) — подставляются только символы
                        (else (zt-uniq (filter (lambda (s) (and (symbol? s) (not (member? s '(pi %i))))) (variables e1))))))
              (binds (map2 (lambda (v i) (list v (+ 2 (modulo (+ (* 37 (+ i 1) (+ k 3)) (* 11 k k) (* 5 i)) 53)))) vs (range (length vs))))
              (s (subst binds e1)))
         (if (and (pair? more) (car more) (not (zt-evaluable? s)))
             'fail
             (zt-value (together s) (and (pair? more) (car more)))))
       (lambda (err) 'fail)))

(define (zt-verdict vals)
  (cond ((any? (lambda (v) (and (not (equal? v 'fail)) (not (equal? v 0)))) vals) 'nonzero)
        ((every? (lambda (v) (equal? v 0)) vals) 'zero)
        (else 'unknown)))

; одна заданная точка: подстановка, simplify, при остатке simplify(expand), затем замкнутая константа
(define (zt-at e rules)
  (let* ((s (if (null? rules) e (subst rules e)))
         (s1 (simplify s))
         (s2 (if (pair? s1) (simplify (expand s1)) s1))
         (v (zt-value s2)))
    (cond ((equal? v 'fail) 'unknown) ((equal? v 0) 'zero) (else 'nonzero))))

; const-zero? на замкнутой константе с башней exp (exp(exp 3)·…) считает минуты (интервалы при 30–75 знаках): весь подбор точек
; идёт под бюджетом (по умолчанию zt-time-limit с; опция (time с)), истёк — 'unknown, а не ожидание
(define zt-time-limit 2)
(define (zt-limited secs thunk)
  (let ((r (call-with-time-limit secs thunk)))
    (if (and (pair? r) (equal? (car r) 'ok)) (cadr r) 'unknown)))

(define (zt-run e vars opts)
  (let ((at (zt-opt-val opts 'at #f)) (secs (zt-opt-val opts 'time zt-time-limit)))
    (if at
        (zt-limited secs (lambda () (zt-at e at)))
        (let ((t (if (zt-opt? opts 'points-only) e (try (together e) (lambda (err) #f)))))
          (cond ((equal? t 0) 'zero)
                ((and t (not (zt-opt? opts 'points-only)) (rational-number? t)) 'nonzero)
                (else
                 (let ((t2 (if t t e)) (n (zt-opt-val opts 'points 3)) (kernels? (zt-opt? opts 'kernels)))
                   (zt-limited secs
                              (lambda ()
                                (if (zt-opt? opts 'zero-only)
                                    (zt-zero-only e vars n kernels?)   ; точки — на исходном e: together раздувает остаток (1,9 тыс. знаков → 20 тыс.)
                                    (zt-verdict (map (lambda (k) (zt-point t2 vars k kernels?)) (range n)))))))))))))

; 'zero-only: вызывающему нужен только ответ «нуль или нет» — точки идут по очереди, счёт кончается на первой, где значение не 0
; (не нуль или подстановка не удалась): 'zero ровно тогда же, когда у zt-verdict (все точки дали 0), иначе 'unknown (без различия
; 'nonzero/'unknown). В поиске Rubi каждая впустую посчитанная точка ≈ 20 мс на кандидата.
(define (zt-zero-only e vars n kernels?)
  (let loop ((k 0))
    (cond ((>= k n) 'zero)
          ((equal? (zt-point e vars k kernels? #t) 0) (loop (+ k 1)))
          (else 'unknown))))

(define (zero-test e vars &rest opts)
  (try (zt-run e vars opts) (lambda (err) 'unknown)))
