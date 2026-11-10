; summation/abramov.lisp — Шаг 21l.4: рациональное суммирование по Абрамову (1975).
; Разложение f(k) = Δg + h (Δg = g(k+1) − g(k)), h — остаток с минимальным знаменателем
; (все множители знаменателя h попарно не переводятся друг в друга целым сдвигом).
; f имеет рациональную первообразную ⇔ h = 0 (⇔ Σ_{k=a}^{b} f = g(b+1) − g(a)).
; Ключ — классы сдвигов неприводимых множителей знаменателя и перенос полюсов:
;   c(k)/q(k+s)^m = c(k−s)/q(k)^m + Δ[ Σ_{i=0}^{s−1} c(k−s+i)/q(k+i)^m ]
; Источники: Абрамов, «Modular algorithms for summation».
; (abramov-decompose f k) → (g . h) | #f (не рациональный терм / сбой)
; (abramov-sum t k lo hi) → замкнутая форма Σ | #f (отказ; неприводимые степени ≥ 2 в h —
;   невычисленная форма, статус unknown: Σ c/(k+α)^m считается через psi/harmonic, но
;   для q степени ≥ 2 без рационального ответа — честное «не знаю»).
; Проверка: тождество Δg + h = f (together + simplify) — не прошла → #f, не ложный ответ.

(module summation
  (export abramov-decompose abramov-sum))

; ---------- вспомогательное ----------

; монический вариант многочлена по k (деление на старший коэффициент); #f если не получается
(define (abramov-monic p k)
  (sum-guard
   (lambda ()
     (let* ((d (degree p k))
            (lc (coeff p k d)))
       (if (number? lc)
           (expand (simplify (list '/ p lc)))
           #f)))))

; j, при котором q2(k) = q1(k+j) (монические одной степени), либо #f.
; Коэффициент при k^(d−1) у q1(k+j) равен c1 + d·j ⇒ j = (c2 − c1)/d; проверка подстановкой.
(define (abramov-shift q1 q2 k)
  (sum-guard
   (lambda ()
     (let ((d1 (degree q1 k)) (d2 (degree q2 k)))
       (if (or (not (= d1 d2)) (= d1 0))
           #f
           (let* ((c1 (coeff q1 k (- d1 1)))
                  (c2 (coeff q2 k (- d2 1)))
                  (j (simplify (list '/ (list '- c2 c1) d1))))
             (if (not (number? j))
                 #f
                 (let ((diff (expand (simplify (list '- (subst (list '= k (list '+ k j)) q1) q2)))))
                   (if (equal? (simplify diff) 0) j #f)))))))))

; классы сдвигов: ((представитель (q . сдвиг) ...) ...) — каждый множитель знаменателя
; попадает в класс первого представителя, в который он сдвигается; иначе новый класс.
; Вход: ((q кратность) ...) из factor-list.
(define (abramov-shift-class factors k)
  (abramov-class-loop factors k '()))

(define (abramov-class-loop factors k classes)
  (if (null? factors)
      classes
      (let ((placed (abramov-place (car (car factors)) classes k)))
        (abramov-class-loop (cdr factors) k placed))))

; поставить множитель q в существующий класс (сдвиг от представителя) или создать новый;
; класс = (rep (q . j) ...) — пары во втором элементе, при добавлении — append в этот список
(define (abramov-place q classes k)
  (if (null? classes)
      (list (list q (list (cons q 0))))
      (let ((j (abramov-shift (car (car classes)) q k)))
        (if j
            (cons (list (car (car classes))
                        (append (car (cdr (car classes))) (list (cons q j))))
                  (cdr classes))
            (let ((rest (abramov-place q (cdr classes) k)))
              (cons (car classes) rest))))))

; ---------- декомпозиция ----------

; (abramov-decompose f k) → (g . h) либо #f. g, h — выражения.
(define (abramov-decompose f k)
  (sum-guard
   (lambda ()
     (let* ((e (together f))
            (num (numer e))
            (den (denom e))
            (qq (sum-guard (lambda () (poly-quotient num den k))))
            (rr (sum-guard (lambda () (poly-remainder num den k)))))
       (if (not (and (and (numeric-poly? num k) (numeric-poly? den k)) qq rr))
           #f
           (let ((g-poly (if (equal? (simplify qq) 0)
                              0
                              ; многочленная часть: g = Σ_{i=0}^{k-1} q(i) (Фаульхабер)
                              (abramov-sum-faulhaber qq k k))))
             (if (equal? (simplify rr) 0)
                 (cons g-poly 0)
                  (abramov-decompose-rest rr den g-poly k))))))))

; Σ_{i=0}^{i2-1} q(i) для многочлена q по k — по мономам (sum-faulhaber из core.lisp)
(define (abramov-sum-faulhaber q k i2)
  (let ((d (degree q k)))
    (if (or (not d) (< d 0))
        0
        (abramov-faulhaber-terms q k i2 d))))

(define (abramov-faulhaber-terms q k i2 d)
  (if (< d 0)
      0
      (let ((c (coeff q k d)))
        (if (equal? (simplify c) 0)
            (abramov-faulhaber-terms q k i2 (- d 1))
            (simplify (list '+
                            (list '* c (sum-faulhaber d 0 (list '- i2 1)))
                            (abramov-faulhaber-terms q k i2 (- d 1))))))))

; перенос полюсов + остаток: apart по k → термы c/q^m; q → представитель класса
; (минимальный сдвиг в классе), offset = сдвиг − минимальный сдвиг; offset > 0:
;   h += c(k−offset)/qrep(k)^m,  g += Σ_{i=0}^{offset−1} c(k−offset+i)/qrep(k+i)^m
(define (abramov-decompose-rest rr den g k)
  (let* ((fl (sum-guard (lambda () (factor-list den))))
         (classes (if fl (abramov-shift-class (cdr fl) k) #f)))
    (if (not classes)
        #f
        (let* ((proper (list '/ rr den)))
          (let ((terms (apart-terms proper k)))
            (let ((res (if (not terms) #f (abramov-shift-poles terms classes k))))
              (if (not res) #f
                  (cons (simplify (list '+ g (car res))) (simplify (cdr res))))))))))

; термы apart: список (c . (q . m)) — c/q^m; разбираем (+ t1 t2 ...) либо одиночный терм
(define (apart-terms e k)
  (apart-terms-raw (expand (simplify (apart e k))) k))

(define (apart-terms-raw e k)
  (cond ((equal? (simplify e) 0) '())
        ((and (op-expr? e) (equal? (car e) '+))
         (append-map (lambda (t) (apart-terms-raw t k)) (cdr e)))
        (else (list (apart-one-term e k)))))

; отрицательная целая степень (^ q -m)
(define (neg-pow-of e)
  (and (op-expr? e) (equal? (car e) (quote ^)) (= (length e) 3)
       (number? (caddr e)) (< (caddr e) 0)))

; один терм c/q^m → (c . (q . m)); формы: c·q^-m, q^-m, c/q, 1/q, длинные произведения
(define (apart-one-term t k)
  (cond
    ((and (op-expr? t) (equal? (car t) (quote *)) (= (length t) 3) (neg-pow-of (caddr t)))
     (cons (cadr t) (cons (cadr (caddr t)) (- (caddr (caddr t))))))
    ((neg-pow-of t) (cons 1 (cons (cadr t) (- (caddr t)))))
    ((and (op-expr? t) (equal? (car t) (quote /)) (= (length t) 3))
     (cons (cadr t) (cons (caddr t) 1)))
    ((and (op-expr? t) (equal? (car t) (quote *)) (> (length t) 3))
     (let ((parts (abramov-split-pow (cdr t) k)))
       (and parts (cons (simplify (car parts)) (cdr parts)))))
    (else #f)))

; множители произведения: (список k-свободных . (q . m)) с одной отрицательной степенью
(define (abramov-split-pow fs k)
  (cond ((null? fs) #f)
        (else
         (let ((p (car fs)))
           (cond ((and (op-expr? p) (equal? (car p) '^) (number? (caddr p)) (< (caddr p) 0))
                  (cons (cdr fs) (cons (cadr p) (- (caddr p)))))
                 (else
                  (let ((r (abramov-split-pow (cdr fs) k)))
                    (and r (cons (cons p (car r)) (cdr r))))))))))



; сдвиги полюсов: для каждого терма — представитель класса знаменателя и offset;
; возвращает (g-add . h) либо #f
(define (abramov-shift-poles terms classes k)
  (abramov-shift-loop terms classes k 0 '()))

(define (abramov-shift-loop terms classes k g-acc h-acc)
  (if (null? terms)
      (cons g-acc (simplify (cons '+ h-acc)))
      (let* ((trm (car terms)))
        (if (not trm)
            #f
            (let* ((c (car trm)) (q (car (cdr trm))) (m (cdr (cdr trm)))
                   (info (abramov-class-of q classes)))
              (if (not info)
                  #f
                  (let* ((qrep (car info))
                         (off (cdr info)))
                    (if (= off 0)
                        ; множитель уже представитель: слагаемое остаётся в h
                        (abramov-shift-loop (cdr terms) classes k g-acc
                                            (cons (list '* c (list '^ qrep (list '- m))) h-acc))
                        ; перенос полюса: h += c(k−off)/qrep(k)^m;
                        ; g += Σ_{i=0}^{off−1} c(k−off+i)/qrep(k+i)^m
                        (let* ((ck (subst (list '= k (list '- k off)) c))
                               (h-term (list '* ck (list '^ qrep (list '- m))))
                               (g-add (abramov-pole-sum c qrep m off k)))
                          (abramov-shift-loop (cdr terms) classes k
                                              (list '+ g-acc g-add)
                                              (cons h-term h-acc)))))))))))

; класс множителя q: (представитель . offset = сдвиг − минимальный сдвиг в классе);
; класс = (rep (q . j) ...) — пары во ВТОРОМ элементе, не в cdr
(define (abramov-class-of q classes)
  (if (null? classes)
      #f
      (let ((hit (assoc q (car (cdr (car classes))))))
        (if hit
            (let* ((group (car (cdr (car classes))))
                   (minj (apply min (map cdr group))))
              (cons (car (car classes)) (- (cdr hit) minj)))
            (abramov-class-of q (cdr classes))))))

; Σ_{i=0}^{s−1} c(k−s+i)/q(k+i)^m — рациональная добавка к g (телескоп по i)
(define (abramov-pole-sum c q m s k)
  (if (= s 0)
      0
      (abramov-pole-sum-in c q m s k 0)))

(define (abramov-pole-sum-in c q m s k i)
  (if (>= i s)
      0
      (simplify (list '+ (list '* (subst (list '= k (list '- (list '+ k i) s)) c)
                                  (list '^ (subst (list '= k (list '+ k i)) q) (list '- m)))
                       (abramov-pole-sum-in c q m s k (+ i 1))))))

; ---------- сумма ----------

; Σ_{k=lo}^{hi} t_k для рационального t: g(hi+1) − g(lo) + Σ h.
; Σ h: термы c/(k+α)^m → psi: Σ = (−1)^m/(m−1)!·(ψ^{(m−1)}(hi+α+1) − ψ^{(m−1)}(lo+α)).
; Неприводимые степени ≥ 2 в h → #f (не знаю, невычисленная форма).
(define (abramov-sum t k lo hi)
  (sum-guard
   (lambda ()
     (let ((dc (abramov-decompose t k)))
       (if (not dc)
           #f
           (let ((g (car dc)) (h (cdr dc)))
             ; проверка тождества Δg + h = t — не прошла → не знаю
             (if (not (abramov-check t g h k))
                 #f
                 (begin
                   (if (step-log-enabled?)
                       (record-step 'abramov-type "Тип: рациональная функция"
                                    "разложение f = Δg + h; знаменатель — по полюсам f"
                                    (sum-form t k lo hi) t 'main))
                   (if (step-log-enabled?)
                       (record-step 'abramov-decompose "Разложение f = Δg + h"
                                    (string-append "g = " (to-string g) "; h = " (to-string h))
                                    (sum-form t k lo hi) g 'main))
                   (if (step-log-enabled?)
                       (record-step 'abramov-check "Проверка Δg + h = f"
                                    "тождество проверено подстановкой k → k+1" t t 'main))
                   (if (equal? (simplify h) 0)
                       (simplify (list '- (subst (list '= k (list '+ hi 1)) g)
                                    (subst (list '= k lo) g)))
                       (abramov-sum-rest g h k lo hi))))))))))

; остаток h ≠ 0: Σ h через psi (только линейные множители k+α, α — число)
(define (abramov-sum-rest g h k lo hi)
  (let ((terms (sum-guard (lambda () (apart-terms h k)))))
    (if (not terms)
        #f
        (let ((hs (abramov-sum-terms terms k lo hi)))
          (if (not hs)
              #f
              (simplify (list '+ (list '- (subst (list '= k (list '+ hi 1)) g)
                                         (subst (list '= k lo) g))
                              hs)))))))

; сумма термов c/(k+α)^m; ψ^{(r)}(x) — (psi x r)
(define (abramov-sum-terms terms k lo hi)
  (if (null? terms)
      0
      (let ((one (abramov-sum-one (car terms) k lo hi)))
        (if one
            (simplify (list '+ one (abramov-sum-terms (cdr terms) k lo hi)))
            #f))))

(define (abramov-sum-one trm k lo hi)
  (sum-guard
   (lambda ()
     (let* ((c (car trm)) (q (car (cdr trm))) (m (cdr (cdr trm)))
            (alpha (abramov-linear-root q k))
            ; нормировка знаменателя: c/(a·k+b)^m = (c/a^m)/(k+α)^m
            (am (expt-q-lc q m k)))
       (and alpha am
            ; Σ c/q^m = (c/a^m)·(−1)^{m−1}/(m−1)!·(ψ^{(m−1)}(hi+α+1) − ψ^{(m−1)}(lo+α))
            (simplify (list '* (list '/ c (list '* am (if (= (mod m 2) 1) 1 -1) (factorial (- m 1))))
                          (list '- (list 'psi (list '+ hi alpha 1) (- m 1))
                                (list 'psi (list '+ lo alpha) (- m 1))))))))))

; a^m для q = a·k + b (старший коэффициент в степени m); #f если не число
(define (expt-q-lc q m k)
  (let ((lc (coeff q k (degree q k))))
    (if (number? lc)
        (if (= m 1) lc (* lc (expt-q-lc q (- m 1) k)))
        #f)))

; корень линейного q = a·k + b = a(k+α) → α = b/a; нелинейный/параметрический → #f
(define (abramov-linear-root q k)
  (sum-guard
   (lambda ()
     (let* ((d (degree q k))
            (lc (coeff q k d)))
       (if (and (= d 1) (number? lc))
           (let ((alpha (simplify (list '/ (coeff q k 0) lc))))
             (if (number? alpha) alpha #f))
           #f)))))

; тождество Δg + h = f
(define (abramov-check f g h k)
  (sum-guard
   (lambda ()
     (let* ((g1 (subst (list '= k (list '+ k 1)) g))
            (lhs (simplify (together (list '+ (list '- g1 g) h))))
            (rhs (simplify (together f))))
       (equal? (simplify (list '- lhs rhs)) 0)))))

; ---------- подключение к каскаду ----------

; Абрамов идёт после Госпера: Госпер закрывает большинство гипергеометрических;
; Абрамов нужен для рациональных без гипергеометрической первообразной (Σ 1/k → psi/harmonic)
(sum-add-strategy
 (lambda (body k lo hi)
   (let ((res (abramov-sum body k lo hi)))
     (if res
         (begin
           (record-step 'abramov "Символьное суммирование: рациональные функции (Абрамов)"
                        "разложение f = Δg + h; h = 0 — телескопирование; остаток — psi/harmonic"
                        (sum-form body k lo hi) res)
           res)
         #f))))
