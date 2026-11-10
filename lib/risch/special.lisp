; risch/special.lisp — таблица специальных функций для неэлементарного остатка: подшаг 21k.6
;
; По умолчанию (integrate e x) неэлементарного интеграла остаётся невычисленной формой + условие risch-nonelementary (21k.4).
; Здесь — ДОПОЛНИТЕЛЬНАЯ информация, ничего в ответах integrate не меняющая:
;   (risch-special e x)  → первообразная, где неэлементарные остатки (integrate R x) заменены специальными функциями, либо #f
;                          (нечего заменять или проверка не прошла). Результат проверяется дифференцированием (sp-ok?).
;   note/причина условия risch-nonelementary дополняется фразой «Через специальную функцию: …» (rs-special-hint).
; Таблица (c — множитель без x; k, a — константы, знак k определяет sign-of):
;   c·exp(−a x²) → c·√π/(2√a)·erf(√a·x);   c·exp(k x²) → c·√π/(2√k)·erfi(√k·x)   (a, k > 0)
;   c·exp(a x)/x → c·Ei(a x);   c/log x → c·li(x);   c·sin(a x)/x → c·Si(a x);   c·cos(a x)/x → c·Ci(a x).
; Шаг SF: собственная таблица производных (sp-dh/sp-diff) удалена — производные erf, erfc, erfi, Ei, li, Si, Ci,
; Shi, Chi заведены в diff (шаг 21k.6′), поэтому sp-ok? проверяет через int-check (diff + simplify/together,
; числовой запасной) — как и остальные стратегии интегратора.

(module risch
  (export risch-special))

; ---------- проверка (Шаг SF: через diff/int-check) ----------
; (sp-ok? F e x) → #t, если d/dx F = e; производные спецфункций понимает diff (21k.6′),
; int-check — точная (simplify/together) либо числовая проверка, как у остальных стратегий
(define (sp-ok? F e x) (int-check F e x))

; ---------- разбор ----------
; u = a·x (a без x, не нуль) → a, иначе #f
(define (sp-lin u x)
  (let ((s (simplify u)))
    (and (polynomial? s x) (= (degree s x) 1) (equal? (simplify (coeff s x 0)) 0)
         (let ((a (simplify (coeff s x 1)))) (and (x-free? a x) (not (equal? a 0)) a)))))

; u = k·x² → k, иначе #f
(define (sp-quad u x)
  (let ((s (simplify u)))
    (and (polynomial? s x) (= (degree s x) 2) (equal? (simplify (coeff s x 0)) 0) (equal? (simplify (coeff s x 1)) 0)
         (let ((k (simplify (coeff s x 2)))) (and (x-free? k x) k)))))

(define (sp-head? f h) (and (pair? f) (equal? (car f) h) (= (length f) 2)))
(define (sp-factors g) (if (and (pair? g) (equal? (car g) '*)) (cdr g) (list g)))
(define (sp-inv-x? f x) (and (pair? f) (equal? (car f) '^) (equal? (cadr f) x) (equal? (caddr f) -1)))

; g = (h u)/x с u = a·x: g — произведение ровно двух множителей x^(−1) и (h u)
(define (sp-over-x g x h)
  (let ((fs (sp-factors g)))
    (and (= (length fs) 2)
         (let ((ix (filter (lambda (f) (sp-inv-x? f x)) fs)) (hs (filter (lambda (f) (sp-head? f h)) fs)))
           (and (= (length ix) 1) (= (length hs) 1) (sp-lin (cadr (car hs)) x))))))

(define (sp-gauss g x)
  (and (sp-head? g 'exp)
       (let ((k (sp-quad (cadr g) x)))
         (and k (not (equal? k 0))
              (let ((s (try (sign-of k) (lambda (err) 'unknown))))
                (cond ((equal? s 'negative)
                       (let ((a (simplify (list '* -1 k))))
                         (simplify (list '* 1/2 (list '^ 'pi 1/2) (list '^ a -1/2) (list 'erf (list '* (list '^ a 1/2) x))))))
                      ((equal? s 'positive)
                       (simplify (list '* 1/2 (list '^ 'pi 1/2) (list '^ k -1/2) (list 'erfi (list '* (list '^ k 1/2) x)))))
                      (else #f)))))))

; (sp-match e x) → c·специальная функция либо #f
(define (sp-match e x)
  (let* ((cs (rs-const-split (simplify e) x)) (c (car cs)) (g (cadr cs))
         (F (or (sp-gauss g x)
                (let ((a (sp-over-x g x 'exp))) (and a (list 'Ei (simplify (list '* a x)))))
                (and (pair? g) (equal? (car g) '^) (equal? (caddr g) -1) (sp-head? (cadr g) 'log) (equal? (cadr (cadr g)) x)
                     (list 'li x))
                (let ((a (sp-over-x g x 'sin))) (and a (list 'Si (simplify (list '* a x)))))
                (let ((a (sp-over-x g x 'cos))) (and a (list 'Ci (simplify (list '* a x))))))))
    (and F (simplify (list '* c F)))))

; ---------- публичное ----------
(define (sp-replace e x)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'integrate) (= (length e) 3) (equal? (caddr e) x))
         (or (sp-match (cadr e) x) e))
        (else (cons (car e) (map (lambda (a) (sp-replace a x)) (cdr e))))))

; (risch-special e x) → F (возможно с оставшимся (integrate R x)) либо #f
(define (risch-special e x)
  (let ((n (integrate e x)))
    (cond ((not (contains-sym? n 'integrate)) n)
          (else (let ((m (simplify (sp-replace n x))))
                  (and (not (equal? m n)) (try (sp-ok? m e x) (lambda (err) #f)) m))))))

; фраза для причины nonelementary: « Через специальную функцию: …» или ""
(define (rs-special-hint R x)
  (try (let ((F (sp-match R x)))
         (if F (string-append "; через специальную функцию: " (integrate::int-mp F) " (функция risch-special).") ""))
       (lambda (err) "")))
