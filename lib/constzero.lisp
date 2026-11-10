; constzero.lisp — проверка нуля замкнутых констант (шаг R4.1): интервалы, тождества, unknown.
;
; (const-zero? c) → #t (доказано c = 0) | #f (доказано c ≠ 0) | unknown. Только доказательства, догадок нет:
;   слой 1–2: точные преобразования — log рационального по простым множителям, exp(Σ k·log p) → ∏ p^k, simplify,
;             точное поле ℚ(α) радикалов (alg-simplify, денестинг), together. Результат 0 ⇒ #t; ненулевое точное число ⇒ #f.
;   слой 3:   строгое интервальное включение (interval.lisp, точность 30 → 50 → 75 знаков): 0 не принадлежит включению ⇒ #f.
;   Точные формы (R4.2): линейные формы по log простых (≠ 0 ⇒ не нуль, Бейкер), арктангенсы рациональных + π (гауссовы числа).
;   Комплексные константы — Re и Im отдельно. R4.2 (внизу файла): const-relations, log-independent?, exp-independent?, const-class, PSLQ.
;   Включение, содержащее 0, нуля НЕ доказывает: в этом случае unknown (не #t по числам).
; Замкнутая константа — числа, pi, e, %i и головы + * ^ - / exp log sin cos tan atan sqrt abs над ними; всё прочее (символ-параметр,
; float) — unknown. Эти пределы сознательные: нуль общих констант неразрешим (Ричардсон; Шануэль), поэтому «не знаю» честнее догадки.
; (const-clean e x) → (e′ unknown?) — убирает из e скрытые нули: x-свободные слагаемые/множители, доказанно равные 0.
; (const-plain? e) — рациональная функция от символов с точными рациональными/алгебраическими числами (together каноничен: ≠ 0 ⇒ ≠ 0).

(module constzero
  (export const-zero? const-closed? const-plain? const-clean const-enclosure const-free-syms
          const-relations const-relation-holds? const-pslq log-independent? exp-independent?
          const-class const-rational-value const-exp-simplify))

(define cz-heads '(+ * ^ - / exp log sin cos tan atan sqrt abs))
(define cz-consts '(pi %pi e %e %i))
(define cz-digits '(30 50 75))
(define cz-cache (make-hash))

(define (cz-exact-number? e)
  (or (integer? e) (equal? (type-of e) 'rational) (equal? (type-of e) 'algebraic)))

; ---------- предикаты ----------
(define (const-closed? e)
  (cond ((cz-exact-number? e) #t)
        ((symbol? e) (member? e cz-consts))
        ((pair? e) (and (member? (car e) cz-heads) (every? const-closed? (cdr e))))
        (else #f)))

(define (const-plain? e)
  (cond ((cz-exact-number? e) #t)
        ((symbol? e) #t)
        ((pair? e)
         (cond ((member? (car e) '(+ * -)) (every? const-plain? (cdr e)))
               ((equal? (car e) '^) (and (= (length e) 3) (integer? (caddr e)) (const-plain? (cadr e))))
               (else #f)))
        (else #f)))

; символы выражения, не считая голов и констант pi e %i
(define (cz-syms-acc e acc)
  (cond ((symbol? e) (if (or (member? e cz-consts) (member? e acc)) acc (cons e acc)))
        ((pair? e) (foldl (lambda (a x) (cz-syms-acc x a)) acc (cdr e)))
        (else acc)))
(define (const-free-syms e) (cz-syms-acc e '()))

; ---------- слой 1–2: точные преобразования ----------
; log положительного рационального: Σ eᵢ·log pᵢ по простым множителям
(define (cz-log-rat r)
  (if (equal? r 1)
      0
      (let ((fn (factor-integer (numer r))) (fd (factor-integer (denom r))))
        (cons '+ (append (map (lambda (pe) (list '* (cadr pe) (list 'log (car pe)))) fn)
                         (map (lambda (pe) (list '* (- 0 (cadr pe)) (list 'log (car pe)))) fd))))))

(define (cz-pos-rat? a) (and (or (integer? a) (equal? (type-of a) 'rational)) (> a 0)))

(define (cz-log a)
  (cond ((cz-pos-rat? a) (try (cz-log-rat a) (lambda (err) (list 'log a))))
        ((and (pair? a) (equal? (car a) '^) (= (length a) 3) (cz-pos-rat? (cadr a))
              (or (integer? (caddr a)) (equal? (type-of (caddr a)) 'rational)))
         (list '* (caddr a) (cz-log (cadr a))))
        ((and (pair? a) (equal? (car a) 'exp) (not (contains-sym? (cadr a) '%i))) (cadr a))   ; log exp s = s для вещественного s
        (else (list 'log a))))

(define (cz-sum-terms s) (if (and (pair? s) (equal? (car s) '+)) (cdr s) (list s)))

; слагаемое k·log p (p простое, k рациональное) → (p k) или #f
(define (cz-log-term t)
  (cond ((and (pair? t) (equal? (car t) 'log) (cz-pos-rat? (cadr t))) (list (cadr t) 1))
        ((and (pair? t) (equal? (car t) '*) (= (length t) 3) (equal? (type-of (cadr t)) 'rational)
              (pair? (caddr t)) (equal? (car (caddr t)) 'log) (cz-pos-rat? (cadr (caddr t))))
         (list (cadr (caddr t)) (cadr t)))
        ((and (pair? t) (equal? (car t) '*) (= (length t) 3) (integer? (cadr t))
              (pair? (caddr t)) (equal? (car (caddr t)) 'log) (cz-pos-rat? (cadr (caddr t))))
         (list (cadr (caddr t)) (cadr t)))
        (else #f)))

; exp(Σ tᵢ): слагаемые k·log p дают p^k, остальное остаётся под exp
(define (cz-exp s)
  (let* ((ts (cz-sum-terms (simplify s)))
         (ps (map cz-log-term ts))
         (hit (filter (lambda (p) p) ps))
         (rest (filter (lambda (t) (not (cz-log-term t))) ts)))
    (if (null? hit)
        (list 'exp s)
        (cons '* (append (map (lambda (p) (list '^ (car p) (cadr p))) hit)
                         (if (null? rest) '() (list (list 'exp (cons '+ rest)))))))))

(define (cz-rw e)
  (if (not (pair? e))
      e
      (let ((args (map cz-rw (cdr e))))
        (cond ((and (equal? (car e) 'log) (= (length args) 1)) (cz-log (simplify (car args))))
              ((and (equal? (car e) 'exp) (= (length args) 1)) (cz-exp (car args)))
              (else (cons (car e) args))))))

; нормальная форма константы
(define (cz-norm c) (simplify (cz-rw c)))

; точное решение: 'zero | 'nonzero | #f
(define (cz-exact-verdict s)
  (cond ((cz-exact-number? s) (if (equal? s 0) 'zero 'nonzero))
        ((equal? (together s) 0) 'zero)
        (else
         (let ((a (try (alg-simplify s) (lambda (err) #f))))
           (cond ((not a) #f)
                 ((cz-exact-number? a) (if (equal? a 0) 'zero 'nonzero))
                 ((equal? a 0) 'zero)
                 (else (cz-form-verdict a)))))))

; линейные формы с точным решением: логарифмы простых (Бейкер/факторизация) и арктангенсы рациональных (гауссовы числа)
(define (cz-form-verdict a)
  (let ((lf (cz-loglin a)))
    (cond ((and lf (null? lf)) 'zero)
          ; c₀ + Σ cₚ·log p = 0 только при всех c = 0: log p трансцендентны и независимы над ℚ̄ (Бейкер; над ℚ — единственность разложения)
          (lf 'nonzero)
          (else (try (cz-atan-verdict a) (lambda (err) #f))))))

; ---------- слой 3: интервальное включение ----------
(define (cz-iv-pow b q)
  (cond ((integer? q) (iv^ b q))
        ((equal? (type-of q) 'rational)
         (if (= (denom q) 2)
             (iv^ (iv-sqrt b) (numer q))
             (iv-exp (cz-round (iv* (iv q q) (iv-log b))))))
        (else (error "cz: степень"))))

(define (cz-iv-abs X)
  (cond ((>= (iv-lo X) 0) X)
        ((<= (iv-hi X) 0) (iv-neg X))
        (else (iv 0 (interval::iv-max-rat (- (iv-lo X)) (iv-hi X))))))

(define (cz-round X)
  (let ((g (^ 10 (+ (iv-precision) 5))))
    (iv (/ (floor (* (iv-lo X) g)) g) (/ (- (floor (* (- (iv-hi X)) g))) g))))

(define (cz-iv e) (cz-round (cz-iv1 e)))

(define (cz-iv1 e)
  (cond ((or (integer? e) (equal? (type-of e) 'rational)) (iv e e))
        ((equal? (type-of e) 'algebraic) (interval::iv-root-interval e (/ 1 (^ 10 (iv-precision)))))
        ((or (equal? e 'pi) (equal? e '%pi)) (iv-pi))
        ((or (equal? e 'e) (equal? e '%e)) (iv-e))
        ((pair? e)
         (let ((h (car e)) (a (cdr e)))
           (cond ((equal? h '+) (apply iv+ (map cz-iv a)))
                 ((equal? h '*) (apply iv* (map cz-iv a)))
                 ((equal? h '-) (if (null? (cdr a)) (iv-neg (cz-iv (car a))) (apply iv- (map cz-iv a))))
                 ((equal? h '/) (if (null? (cdr a)) (iv/ (iv 1 1) (cz-iv (car a))) (apply iv/ (map cz-iv a))))
                 ((equal? h '^)
                  (let ((q (cadr a)))
                    (if (or (integer? q) (equal? (type-of q) 'rational))
                        (cz-iv-pow (cz-iv (car a)) q)
                        (iv-exp (cz-round (iv* (cz-iv q) (iv-log (cz-iv (car a)))))))))
                 ((equal? h 'sqrt) (iv-sqrt (cz-iv (car a))))
                 ((equal? h 'exp) (iv-exp (cz-iv (car a))))
                 ((equal? h 'log) (iv-log (cz-iv (car a))))
                 ((equal? h 'sin) (iv-sin (cz-iv (car a))))
                 ((equal? h 'cos) (iv-cos (cz-iv (car a))))
                 ((equal? h 'tan) (let ((X (cz-iv (car a)))) (iv/ (iv-sin X) (iv-cos X))))
                 ((equal? h 'atan) (iv-atan (cz-iv (car a))))
                 ((equal? h 'abs) (cz-iv-abs (cz-iv (car a))))
                 (else (error "cz: операция" h)))))
        (else (error "cz: выражение" e))))

; (const-enclosure c digits) → интервал (iv lo hi) со строгим включением значения c, либо #f (не вычислимо: %i, ветви, деление на 0)
(define (const-enclosure c digits)
  (let ((old (iv-precision)))
    (iv-set-precision! digits)
    (unwind-protect
      (try (cz-iv c) (lambda (err) #f))
      (iv-set-precision! old))))

(define (cz-iv-nonzero? c digits)
  (let ((X (const-enclosure c digits)))
    (and X (or (> (iv-lo X) 0) (< (iv-hi X) 0)))))

(define (cz-iv-loop c ds)
  (cond ((null? ds) #f)
        ((cz-iv-nonzero? c (car ds)) #t)
        (else (cz-iv-loop c (cdr ds)))))

; ---------- комплексные константы: Re и Im по отдельности ----------
; (cz-cx e) → (re im) — вещественные замкнутые выражения — либо #f (ветвь неясна). Знак вещественного — по интервальному включению.
(define (cz-sign a)                                                  ; 1, -1 или #f (нуль/не решено)
  (let ((X (const-enclosure a 30)))
    (cond ((not X) #f) ((> (iv-lo X) 0) 1) ((< (iv-hi X) 0) -1) (else #f))))
(define (cx-mul p q)
  (list (list '+ (list '* (car p) (car q)) (list '* -1 (cadr p) (cadr q)))
        (list '+ (list '* (car p) (cadr q)) (list '* (cadr p) (car q)))))
(define (cx-pow p n)                                                 ; n ≥ 1
  (if (= n 1) p (cx-mul p (cx-pow p (- n 1)))))
(define (cx-div p q)
  (let ((d (list '+ (list '^ (car q) 2) (list '^ (cadr q) 2))))
    (let ((m (cx-mul p (list (car q) (list '* -1 (cadr q))))))
      (list (list '* (car m) (list '^ d -1)) (list '* (cadr m) (list '^ d -1))))))
(define (cz-cx-pow b q)
  (cond ((and (integer? q) (> q 0) (<= q 64)) (cx-pow b q))
        ((and (integer? q) (< q 0) (>= q -64)) (cx-div (list 1 0) (cx-pow b (- q))))
        ((integer? q) (if (= q 0) (list 1 0) #f))
        ((not (equal? (cadr b) 0)) #f)                                ; комплексное основание, дробная степень — не берём
        ((equal? (cz-sign (car b)) 1) (list (list '^ (car b) q) 0))
        ((and (equal? (cz-sign (car b)) -1) (equal? q 1/2)) (list 0 (list '^ (list '* -1 (car b)) 1/2)))
        (else #f)))
(define (cz-cx e)
  (cond ((or (integer? e) (equal? (type-of e) 'rational) (equal? (type-of e) 'algebraic)) (list e 0))
        ((equal? e '%i) (list 0 1))
        ((member? e '(pi %pi e %e)) (list e 0))
        ((not (pair? e)) #f)
        (else
         (let ((h (car e)) (a (cdr e)))
           (cond ((equal? h '+) (let ((ps (map cz-cx a)))
                                  (and (every? (lambda (p) p) ps)
                                       (list (cons '+ (map car ps)) (cons '+ (map cadr ps))))))
                 ((equal? h '*) (let ((ps (map cz-cx a)))
                                  (and (every? (lambda (p) p) ps) (foldl cx-mul (list 1 0) ps))))
                 ((equal? h '-) (let ((ps (map cz-cx a)))
                                  (and (every? (lambda (p) p) ps)
                                       (if (null? (cdr ps))
                                           (list (list '* -1 (car (car ps))) (list '* -1 (cadr (car ps))))
                                           (list (cons '+ (cons (car (car ps)) (map (lambda (p) (list '* -1 (car p))) (cdr ps))))
                                                 (cons '+ (cons (cadr (car ps)) (map (lambda (p) (list '* -1 (cadr p))) (cdr ps)))))))))
                 ((equal? h '/) (let ((ps (map cz-cx a)))
                                  (and (every? (lambda (p) p) ps)
                                       (if (null? (cdr ps)) (cx-div (list 1 0) (car ps)) (cx-div (car ps) (cadr ps))))))
                 ((equal? h '^) (let ((b (cz-cx (car a))) (q (cadr a)))
                                  (and b (or (integer? q) (equal? (type-of q) 'rational)) (cz-cx-pow b q))))
                 ((equal? h 'sqrt) (cz-cx (list '^ (car a) 1/2)))
                 ((equal? h 'exp) (let ((p (cz-cx (car a))))
                                    (and p (list (list '* (list 'exp (car p)) (list 'cos (cadr p)))
                                                 (list '* (list 'exp (car p)) (list 'sin (cadr p)))))))
                 ((equal? h 'log) (let ((p (cz-cx (car a))))
                                    (and p (equal? (cadr p) 0)
                                         (cond ((equal? (cz-sign (car p)) 1) (list (list 'log (car p)) 0))
                                               ((equal? (cz-sign (car p)) -1) (list (list 'log (list '* -1 (car p))) 'pi))
                                               (else #f)))))
                 ((member? h '(sin cos tan atan abs))
                  (let ((p (cz-cx (car a)))) (and p (equal? (cadr p) 0) (list (list h (car p)) 0))))
                 (else #f))))))

; Re = Im = 0 ⇔ c = 0. 'none — разложение не вышло
(define (cz-complex-zero s)
  (let ((p (try (cz-cx s) (lambda (err) #f))))
    (if (not p)
        'none
        (let ((r (const-zero? (car p))) (i (const-zero? (cadr p))))
          (cond ((or (equal? r #f) (equal? i #f)) #f)
                ((and (equal? r #t) (equal? i #t)) #t)
                (else 'unknown))))))

; ---------- главный предикат ----------
(define (const-zero? c)
  (let ((hit (hash-ref cz-cache c (quote none))))
    (if (equal? hit (quote none))
        (let ((r (cz-decide c))) (hash-set! cz-cache c r) r)
        hit)))

(define (cz-decide c)
  (cond ((integer? c) (equal? c 0))
        ((not (const-closed? c)) 'unknown)
        (else
         (let* ((s (try (cz-norm c) (lambda (err) c)))
                (v (cz-exact-verdict s)))
           (cond ((equal? v 'zero) #t)
                 ((equal? v 'nonzero) #f)
                 ((cz-iv-loop s cz-digits) #f)
                 ((and (not (const-enclosure s 30)) (not (equal? (cz-complex-zero s) 'none)))
                  (cz-complex-zero s))
                 ((and (not (equal? s c)) (not (const-enclosure s 30)) (cz-iv-loop c cz-digits)) #f)
                 (else 'unknown))))))

; ---------- очистка скрытых нулей ----------
(define cz-clean-unknown #f)

; константа: скрытый нуль → 0; unknown запоминается
(define (cz-clean-const c)
  (if (or (const-plain? c) (not (const-closed? c)))
      c
      (let ((z (const-zero? c)))
        (cond ((equal? z #t) 0)
              ((equal? z #f)
               ; скрытое рациональное (log 6/(log 2 + log 3) = 1) заменяется числом; кандидат без доказательства — unknown
               (let ((v (const-rational-value c)))
                 (cond ((cz-rat? v) v)
                       ((equal? v 'unknown) (set! cz-clean-unknown #t) c)
                       (else c))))
              (else (set! cz-clean-unknown #t) c)))))

(define (cz-clean-node e x)
  (cond ((not (pair? e)) e)
        ((x-free? e x) (cz-clean-const e))
        ((member? (car e) '(+ *))
         (let* ((free (filter (lambda (a) (x-free? a x)) (cdr e)))
                (dep (filter (lambda (a) (not (x-free? a x))) (cdr e)))
                (dep2 (map (lambda (a) (cz-clean-node a x)) dep))
                (c (if (null? free) (if (equal? (car e) '+) 0 1) (cz-clean-const (cons (car e) free)))))
           (cond ((and (equal? (car e) '*) (equal? c 0)) 0)
                 ((equal? (car e) '+) (cons '+ (cons c dep2)))
                 (else (cons '* (cons c dep2))))))
        (else (cons (car e) (map (lambda (a) (cz-clean-node a x)) (cdr e))))))

; (const-clean e x) → (e′ unknown?)
(define (const-clean e x)
  (set! cz-clean-unknown #f)
  (let* ((r (cz-clean-node e x)) (unk cz-clean-unknown))
    (list (if (equal? r e) e (simplify r)) unk)))

; ================= R4.2: соотношения между константами =================
; Опора на доказанные теоремы (ссылки — в комментариях к функциям):
;   Бейкер (1966–67): если log α₁ … log αₙ линейно независимы над ℚ (α — алгебраические), то 1, log α₁ … log αₙ линейно независимы над ℚ̄.
;     Для рациональных αᵢ независимость над ℚ — мультипликативная независимость, т.е. ранг матрицы показателей простых множителей (точно).
;   Линдеман — Вейерштрасс: e^α₁ … e^αₙ алгебраически независимы над ℚ ⇔ α алгебраические и ℚ-линейно независимы.
;   Эрмит (e), Линдеман (π), Гельфонд (e^π = (−1)^{−i}), Гельфонд — Шнайдер (a^b, a ≠ 0, 1, b алгебраическое иррациональное) — трансцендентность.
;   Открыто (поэтому unknown): e + π, e·π, π^e, e^e, log π, соотношения между e и π (Шануэль).

; ---------- линейные формы по логарифмам простых ----------
(define (cz-rat? x) (or (integer? x) (equal? (type-of x) 'rational)))

(define (cz-lin-term t)                                              ; → (ключ . коэффициент) | #f; ключ 1 — рациональная часть
  (cond ((cz-rat? t) (cons 1 t))
        ((and (pair? t) (equal? (car t) 'log) (integer? (cadr t)) (> (cadr t) 1) (prime? (cadr t))) (cons (cadr t) 1))
        ((and (pair? t) (equal? (car t) '*) (= (length t) 3) (cz-rat? (cadr t)))
         (let ((u (cz-lin-term (caddr t)))) (and u (not (equal? (car u) 1)) (= (cdr u) 1) (cons (car u) (cadr t)))))
        (else #f)))

(define (cz-merge-lin ps acc)
  (cond ((null? ps) (filter (lambda (p) (not (= (cdr p) 0))) (reverse acc)))
        ((assoc (car (car ps)) acc)
         (cz-merge-lin (cdr ps) (map (lambda (q) (if (equal? (car q) (car (car ps))) (cons (car q) (+ (cdr q) (cdr (car ps)))) q)) acc)))
        (else (cz-merge-lin (cdr ps) (cons (car ps) acc)))))

; (cz-loglin e) → ((p . коэф) …) без нулевых, либо #f (не линейная форма от log простых и рационального числа)
(define (cz-loglin e)
  (let ((ps (map cz-lin-term (cz-sum-terms e))))
    (and (every? (lambda (p) p) ps) (cz-merge-lin ps '()))))

; ---------- ядро целочисленной матрицы (точная арифметика над ℚ) ----------
(define (cz-unit k i) (map (lambda (j) (if (= i j) 1 0)) (range k)))
(define (cz-row-sub r p f) (map2 (lambda (a b) (- a (* f b))) r p))
(define (cz-find-idx pred l i) (cond ((null? l) #f) ((pred (car l)) i) (else (cz-find-idx pred (cdr l) (+ i 1)))))
(define (cz-elim rows c m)
  (if (= c m)
      rows
      (let ((i (cz-find-idx (lambda (r) (not (= (nth r c) 0))) rows 0)))
        (if (not i)
            (cz-elim rows (+ c 1) m)
            (let* ((p (nth rows i)) (others (append (take rows i) (drop rows (+ i 1)))))
              (cz-elim (map (lambda (r) (cz-row-sub r p (/ (nth r c) (nth p c)))) others) (+ c 1) m))))))
(define (cz-primitive v)
  (let* ((den (foldl lcm 1 (map denom v))) (w (map (lambda (a) (* a den)) v)) (g (foldl gcd 0 w)))
    (map (lambda (a) (quotient a g)) w)))
; целые n с Σ nᵢ·rowᵢ = 0 (базис над ℚ, примитивные векторы); rows — строки длины m
(define (cz-left-kernel rows m)
  (let* ((k (length rows))
         (aug (map2 (lambda (r i) (append r (cz-unit k i))) rows (range k))))
    (map (lambda (r) (cz-primitive (drop r m))) (cz-elim aug 0 m))))

(define (cz-forms->rows forms)
  (let ((keys (foldl (lambda (acc f) (foldl (lambda (a p) (if (member? (car p) a) a (append a (list (car p))))) acc f)) '() forms)))
    (list (map (lambda (f) (map (lambda (k) (let ((p (assoc k f))) (if p (cdr p) 0))) keys)) forms) (length keys))))

; (const-relation-holds? cs ns) — Σ nᵢ·cᵢ = 0: #t / #f / unknown (доказательство через const-zero?)
(define (const-relation-holds? cs ns)
  (const-zero? (cons '+ (map2 (lambda (c n) (list '* n c)) cs ns))))

(define (cz-forms-of cs)
  (map (lambda (c) (and (const-closed? c) (try (cz-loglin (cz-norm c)) (lambda (e) #f)))) cs))

; (log-independent? cs) — cs — логарифмы рациональных (log a), …; #t — ℚ-линейно независимы (ранг матрицы показателей простых = n;
; по Бейкеру тогда независимы и над ℚ̄), #f — есть нетривиальное целое соотношение, unknown — не формы от log простых.
(define (log-independent? cs)
  (let ((forms (cz-forms-of cs)))
    (if (every? (lambda (f) f) forms)
        (let ((rm (cz-forms->rows forms)))
          (if (null? (cz-left-kernel (car rm) (cadr rm))) #t #f))
        'unknown)))

; ---------- PSLQ (численный генератор кандидатов; не доказательство) ----------
(define cz-gamma 11547005383792515/10000000000000000)                 ; √(4/3)
(define (cz-abs x) (if (< x 0) (- 0 x) x))
(define (cz-range a b) (map (lambda (k) (+ a k)) (range (- b a))))     ; a … b−1 (range — один аргумент)
(define (cz-vswap! v i j) (let ((t (vref v i))) (vset! v i (vref v j)) (vset! v j t)))
(define (cz-mat n m f) (list->vector (map (lambda (i) (list->vector (map (lambda (j) (f i j)) (range m)))) (range n))))
(define (cz-mref M i j) (vref (vref M i) j))
(define (cz-mset! M i j x) (vset! (vref M i) j x))

(define (cz-argmax-h H n)
  (let loop ((i 1) (best 0) (bv (* cz-gamma (cz-abs (cz-mref H 0 0)))))
    (if (>= i (- n 1))
        best
        (let ((v (* (^ cz-gamma (+ i 1)) (cz-abs (cz-mref H i i)))))
          (if (> v bv) (loop (+ i 1) i v) (loop (+ i 1) best bv))))))

; строка i, столбец j: t = nint(H[i][j]/H[j][j]); y[j] += t·y[i]; H[i][0..j] −= t·H[j][0..j]; A[i] −= t·A[j]; B[·][j] += t·B[·][i]
(define (cz-pslq-reduce! y H A B n rnd)
  (for-each
   (lambda (i)
     (for-each
      (lambda (jj)
        (let ((j (- (- i 1) jj)))
          (if (not (= (cz-mref H j j) 0))
              (let ((t (floor (+ (/ (cz-mref H i j) (cz-mref H j j)) 1/2))))
                (if (not (= t 0))
                    (begin
                      (vset! y j (rnd (+ (vref y j) (* t (vref y i)))))
                      (for-each (lambda (k) (cz-mset! H i k (rnd (- (cz-mref H i k) (* t (cz-mref H j k)))))) (range (+ j 1)))
                      (for-each (lambda (k) (cz-mset! A i k (- (cz-mref A i k) (* t (cz-mref A j k))))) (range n))
                      (for-each (lambda (k) (cz-mset! B k j (+ (cz-mref B k j) (* t (cz-mref B k i))))) (range n))))))))
      (range i)))
   (cz-range 1 n)))

; шаг: обмен m, m+1 и поворот Givens, убирающий H[m][m+1]
(define (cz-pslq-swap! y H A B n m rnd sq)
  (cz-vswap! y m (+ m 1))
  (cz-vswap! A m (+ m 1))
  (cz-vswap! H m (+ m 1))
  (for-each (lambda (k) (let ((t (cz-mref B k m))) (cz-mset! B k m (cz-mref B k (+ m 1))) (cz-mset! B k (+ m 1) t))) (range n))
  (if (<= m (- n 3))
      (let ((t0 (sq (+ (* (cz-mref H m m) (cz-mref H m m)) (* (cz-mref H m (+ m 1)) (cz-mref H m (+ m 1)))))))
        (if (not (= t0 0))
            (let ((t1 (/ (cz-mref H m m) t0)) (t2 (/ (cz-mref H m (+ m 1)) t0)))
              (for-each
               (lambda (i)
                 (let ((t3 (cz-mref H i m)) (t4 (cz-mref H i (+ m 1))))
                   (cz-mset! H i m (rnd (+ (* t1 t3) (* t2 t4))))
                   (cz-mset! H i (+ m 1) (rnd (+ (* -1 t2 t3) (* t1 t4))))))
               (cz-range m n)))))))

(define (cz-pslq-loop y H A B n rnd sq tol it maxit)
  (cz-pslq-reduce! y H A B n rnd)
  (let ((j (cz-find-idx (lambda (v) (< (cz-abs v) tol)) (vector->list y) 0)))
    (cond (j (map (lambda (k) (cz-mref B k j)) (range n)))
          ((>= it maxit) #f)
          (else (cz-pslq-swap! y H A B n (cz-argmax-h H n) rnd sq)
                (cz-pslq-loop y H A B n rnd sq tol (+ it 1) maxit)))))

; (cz-pslq-run xs D maxit) → целый вектор-кандидат (Σ rₖ·xₖ ≈ 0) или #f; xs — рациональные, D — рабочие знаки
(define (cz-pslq-run xs D maxit)
  (let* ((n (length xs)) (G (^ 10 D))
         (rnd (lambda (q) (/ (floor (+ (* q G) 1/2)) G)))
         (sq (lambda (q) (/ (interval::iv-isqrt (floor (* q G G))) G)))
         (y (list->vector xs))
         (s (make-vector n 0)))
    (let sloop ((k (- n 1)) (acc 0))
      (if (>= k 0)
          (let ((a (+ acc (* (vref y k) (vref y k))))) (vset! s k (sq a)) (sloop (- k 1) a))))
    (let ((t0 (vref s 0)))
      (if (= t0 0)
          #f
          (begin
            (for-each (lambda (i) (vset! y i (rnd (/ (vref y i) t0))) (vset! s i (rnd (/ (vref s i) t0)))) (range n))
            (let ((H (cz-mat n (- n 1)
                             (lambda (i j) (cond ((< i j) 0)
                                                 ((= i j) (rnd (/ (vref s (+ j 1)) (vref s j))))
                                                 (else (rnd (/ (- 0 (* (vref y i) (vref y j))) (* (vref s j) (vref s (+ j 1))))))))))
                  (A (cz-mat n n (lambda (i j) (if (= i j) 1 0))))
                  (B (cz-mat n n (lambda (i j) (if (= i j) 1 0)))))
              (cz-pslq-loop y H A B n rnd sq (/ 1 (^ 10 (quotient D 2))) 0 maxit)))))))

; (const-pslq cs digits) → целый вектор-кандидат с Σ nᵢ·cᵢ ≈ 0 (digits знаков, коэффициенты умеренные) или #f. НЕ доказательство.
(define (const-pslq cs digits)
  (let ((xs (map (lambda (c) (let ((X (const-enclosure c digits))) (and X (iv-mid X)))) cs)))
    (if (or (< (length cs) 2) (not (every? (lambda (x) x) xs)))
        #f
        (let ((r (try (cz-pslq-run xs (+ digits 10) 400) (lambda (err) #f))))
          (and r (not (every? (lambda (a) (= a 0)) r))
               (< (cz-abs (foldl + 0 (map2 * r xs))) (/ 1 (^ 10 (quotient digits 2))))
               r)))))

; (const-relations cs) → список ДОКАЗАННЫХ целочисленных соотношений Σ nᵢ·cᵢ = 0 (векторы n). Логарифмы рациональных (и рациональная часть) —
; точно по простым множителям (базис ядра над ℚ); иначе PSLQ предлагает кандидат, который проходит только после const-zero? = #t.
(define (const-relations cs)
  (let ((forms (cz-forms-of cs)))
    (if (every? (lambda (f) f) forms)
        (let ((rm (cz-forms->rows forms)))
          (filter (lambda (n) (equal? (const-relation-holds? cs n) #t)) (cz-left-kernel (car rm) (cadr rm))))
        (let ((r (const-pslq cs 45)))
          (if (and r (equal? (const-relation-holds? cs r) #t)) (list r) '())))))

; exp(c) в нормальной форме: слагаемые k·log p дают p^k (exp(x + log 2) → 2·exp x; exp(2 log 3 + log 2) → 18)
(define (const-exp-simplify c) (simplify (cz-rw (list 'exp c))))

; ---------- рациональность константы ----------
; самое простое рациональное в [lo, hi] (0 < lo ≤ hi)
(define (cz-simplest lo hi)
  (let ((fl (floor lo)))
    (cond ((= fl lo) fl)
          ((< fl (floor hi)) (+ fl 1))
          (else (+ fl (/ 1 (cz-simplest (/ 1 (- hi fl)) (/ 1 (- lo fl)))))))))
(define (cz-simplest-in X)
  (cond ((and (<= (iv-lo X) 0) (>= (iv-hi X) 0)) 0)
        ((> (iv-lo X) 0) (cz-simplest (iv-lo X) (iv-hi X)))
        (else (- 0 (cz-simplest (- 0 (iv-hi X)) (- 0 (iv-lo X)))))))

; (const-rational-value c) → рациональное r (доказано c = r) | 'no (c — не рациональное со знаменателем ≤ 10^12: трансцендентное, иррациональное
; алгебраическое, либо включение 50 знаков не содержит такой дроби) | unknown (кандидат есть, равенство не доказано, или константа не замкнута)
(define (const-rational-value c)
  (cond ((cz-rat? c) c)
        ((not (const-closed? c)) 'unknown)
        (else
         (let ((s (try (cz-norm c) (lambda (err) c))))
           (cond ((cz-rat? s) s)
                 ((equal? (type-of s) 'algebraic) 'no)
                 ((equal? (const-class s) 'transcendental) 'no)
                 (else
                  (let ((X (const-enclosure s 50)))
                    (if (not X)
                        'unknown
                        (let ((r (cz-simplest-in X)))
                          (cond ((> (denom r) 1000000000000) 'no)
                                ((equal? (const-zero? (list '+ s (list '* -1 r))) #t) r)
                                (else 'unknown)))))))))))

; ---------- классификация: алгебраическое / трансцендентное / неизвестно ----------
(define (cz-alg-expr? e)
  (cond ((cz-exact-number? e) #t)
        ((equal? e '%i) #t)
        ((pair? e)
         (cond ((member? (car e) '(+ * - /)) (every? cz-alg-expr? (cdr e)))
               ((equal? (car e) 'sqrt) (cz-alg-expr? (cadr e)))
               ((equal? (car e) '^) (and (= (length e) 3) (cz-rat? (caddr e)) (cz-alg-expr? (cadr e))))
               (else #f)))
        (else #f)))

(define (cz-ipi-multiple? a)                                         ; a = q·i·π (q ∈ ℚ): e^a — корень из единицы
  (let ((s (simplify a)))
    (or (equal? s 0)
        (and (pair? s) (equal? (car s) '*)
             (let ((fs (cdr s)))
               (and (every? (lambda (f) (or (cz-rat? f) (equal? f '%i) (equal? f 'pi))) fs)
                    (member? '%i fs) (member? 'pi fs)))))))

; (const-class c) → algebraic | transcendental | unknown. Только по доказанным теоремам (см. шапку раздела).
(define (const-class c)
  (let ((s (if (const-closed? c) (try (cz-norm c) (lambda (err) c)) c)))
    (cond ((not (const-closed? s)) 'unknown)
          ((cz-alg-expr? s) 'algebraic)
          ((member? s '(pi %pi e %e)) 'transcendental)                  ; Эрмит, Линдеман
          ((not (pair? s)) 'unknown)
          (else (cz-class-node s)))))

(define (cz-nonzero? a) (equal? (const-zero? a) #f))
(define (cz-count-tr cl) (length (filter (lambda (k) (equal? k 'transcendental)) cl)))
(define (cz-class-node s)
  (let ((h (car s)) (a (cdr s)))
    (cond ((equal? h 'exp)
           (let ((u (car a)))
             (cond ((cz-ipi-multiple? u) 'algebraic)
                   ((and (cz-alg-expr? u) (cz-nonzero? u)) 'transcendental)      ; Эрмит — Линдеман
                   ((member? u '(pi %pi)) 'transcendental)                       ; Гельфонд (1934): e^π = (−1)^(−i)
                   (else 'unknown))))
          ((equal? h 'log)
           (let ((u (car a)))
             (if (and (cz-alg-expr? u) (cz-nonzero? u) (cz-nonzero? (list '+ u -1)))
                 'transcendental                                                 ; e^(log u) = u было бы алгебраическим
                 'unknown)))
          ((member? h '(sin cos tan atan))
           (let ((u (car a)))
             (if (and (cz-alg-expr? u) (cz-nonzero? u) (not (contains-sym? u '%i))) 'transcendental 'unknown)))   ; через e^(iu), Линдеман
          ((equal? h '^)
           (let ((b (car a)) (q (cadr a)))
             (cond ((and (cz-alg-expr? b) (cz-alg-expr? q) (not (contains-sym? s '%i))
                         (cz-nonzero? b) (cz-nonzero? (list '+ b -1))
                         (equal? (const-rational-value q) 'no))
                    'transcendental)                                             ; Гельфонд — Шнайдер
                   ((and (cz-rat? q) (equal? (const-class b) 'transcendental)) 'transcendental)
                   (else 'unknown))))
          ((equal? h '+)
           (let ((cl (map const-class a)))
             (cond ((member? 'unknown cl) 'unknown)
                   ((= (cz-count-tr cl) 1) 'transcendental)                      ; алгебраическое + трансцендентное
                   (else 'unknown))))                                            ; e + π — открытая проблема
          ((equal? h '*)
           (let ((cl (map const-class a)) (alg (filter cz-alg-expr? a)))
             (cond ((member? 'unknown cl) 'unknown)
                   ((and (= (cz-count-tr cl) 1) (every? cz-nonzero? alg)) 'transcendental)
                   (else 'unknown))))
          (else 'unknown))))

; ---------- независимость экспонент (Линдеман — Вейерштрасс) ----------
; координаты алгебраических выражений в ℚ(γ) (квадратные радикалы, в том числе i): список векторов одной длины или #f
(define (cz-alg-coords es)
  (try
   (let* ((es1 (map sqrt-denest es))
          (rads (foldl denest::dn-union '() (map denest::dn-radicals es1))))
     (if (null? rads)
         (map (lambda (e) (list (simplify e))) es1)
         (let* ((fb (denest::dn-build-field rads)) (F (car fb)) (pairs (cadr fb))
                (cs (map (lambda (e) (denest::dn-eval F e pairs)) es1))
                (w (foldl max 1 (map length cs))))
           (map (lambda (v) (append v (map (lambda (i) 0) (range (- w (length v)))))) cs))))
   (lambda (err) #f)))

; (exp-independent? as) — as — алгебраические константы α₁ … αₙ: #t — e^α₁ … e^αₙ алгебраически независимы (α ℚ-линейно независимы;
; Линдеман — Вейерштрасс), #f — есть соотношение Σ nᵢαᵢ = 0 (тогда ∏ e^(nᵢαᵢ) = 1), unknown — не алгебраические (π, e, …) либо не вышло
(define (exp-independent? as)
  (if (not (every? (lambda (a) (and (const-closed? a) (cz-alg-expr? a))) as))
      'unknown
      (let ((cs (cz-alg-coords as)))
        (if (not cs)
            'unknown
            (if (null? (cz-left-kernel cs (length (car cs)))) #t #f)))))

; ---------- арктангенсы рациональных: точное решение через гауссовы числа ----------
; S = Σ Qᵢ·atan rᵢ + M·π (целые Q, M после умножения на общий знаменатель). z = ∏ (1 + i·rᵢ)^Qᵢ — гауссово рациональное, arg z ≡ Σ Qᵢ atan rᵢ (mod 2π).
; S = 0 ⇒ z вещественно со знаком (−1)^M; обратно, тогда S ∈ 2πℤ, и интервальное включение S в (−6/d, 6/d) доказывает S = 0.
; Не выполнено условие на z ⇒ S ∉ 2πℤ ⇒ S ≠ 0 (точно).
(define (cz-atan-term t)                                             ; → (ключ . коэффициент): ключ pi или рациональное r (atan r)
  (cond ((member? t '(pi %pi)) (cons 'pi 1))
        ((and (pair? t) (equal? (car t) 'atan) (cz-rat? (cadr t))) (cons (cadr t) 1))
        ((and (pair? t) (equal? (car t) '*) (= (length t) 3) (cz-rat? (cadr t)))
         (let ((u (cz-atan-term (caddr t)))) (and u (= (cdr u) 1) (cons (car u) (cadr t)))))
        (else #f)))

(define (cg-mul p q) (list (- (* (car p) (car q)) (* (cadr p) (cadr q))) (+ (* (car p) (cadr q)) (* (cadr p) (car q)))))
(define (cg-pow p n) (cond ((= n 0) (list 1 0)) ((= n 1) p) (else (cg-mul p (cg-pow p (- n 1))))))

(define (cz-atan-verdict s)
  (let ((ps (map cz-atan-term (cz-sum-terms s))))
    (if (not (every? (lambda (p) p) ps))
        #f
        (let* ((m (cz-merge-lin (map (lambda (p) (cons (car p) (cdr p))) ps) '()))
               (d (foldl lcm 1 (map (lambda (p) (denom (cdr p))) m)))
               (M (let ((p (assoc 'pi m))) (if p (* d (cdr p)) 0)))
               (z (foldl (lambda (acc p)
                           (if (equal? (car p) 'pi)
                               acc
                               (let ((Q (* d (cdr p))))
                                 (cg-mul acc (cg-pow (if (> Q 0) (list 1 (car p)) (list 1 (- 0 (car p)))) (cz-abs Q))))))
                         (list 1 0) m)))
          (if (not (and (= (cadr z) 0) (equal? (if (> (car z) 0) 1 -1) (if (= (remainder M 2) 0) 1 -1))))
              'nonzero
              (let ((X (const-enclosure s 30)) (b (/ 6 d)))
                (cond ((not X) #f)
                      ((and (> (iv-lo X) (- 0 b)) (< (iv-hi X) b)) 'zero)
                      ((or (> (iv-lo X) 0) (< (iv-hi X) 0)) 'nonzero)
                      (else #f))))))))
