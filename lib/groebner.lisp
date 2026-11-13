; groebner.lisp — базисы Грёбнера (шаг 21i, правило «сначала Lisp»). Алгоритм Бухбергера в варианте GROEBNERNEWS2
; Беккера–Вейспфеннинга (1993, с. 232; структура Бухбергера с нормальной стратегией):
; начальная интерредукция (BW с. 203), вставка образующих по возрастанию старших мономов, критерии Бухбергера
; (произведения и цепной — в форме Гебауэра–Мёллера: M, F, B_k), нормальная стратегия выбора пар (или sugar),
; приведённый базис (единственный для идеала и порядка).
;
; Представление (внутреннее, только в этом модуле):
;   моном   — список (d e1 … en): d — полная степень (кэш), ei — показатель i-й переменной из списка vars;
;   терм    — (c d e1 … en) = (cons коэффициент моном), коэффициент — рациональное число;
;   многочлен — список термов по УБЫВАНИЮ мономов в текущем порядке; нуль — '().
; Порядки мономов: lex, grlex, grevlex (переменные: первая в списке — старшая); для исключения — блочный
; (block k): сначала grevlex по первым k переменным, при равенстве — grevlex по остальным.
; Коэффициенты — только рациональные числа (символы вне списка переменных — ошибка; параметры не поддерживаются,
; кроме normal-form: там лишние символы становятся младшими переменными).
;
; API: (groebner многочлены переменные [порядок]) → приведённый базис списком выражений (по убыванию старших мономов);
;      (normal-form f образующие переменные [порядок]) → нормальная форма f по модулю идеала образующих;
;      (eliminate многочлены исключаемые остальные) → образующие идеала исключения I ∩ ℚ[остальные];
;      (fglm базис переменные из в) → тот же идеал в другом порядке (нульмерный; шаг 21i'' (2), ниже);
;      (zero-dim? базис переменные [порядок]); (groebner-lex многочлены переменные) — grevlex + FGLM, иначе прямой lex.
; Многочлен — выражение или уравнение (= a b) (означает a − b). Порядок по умолчанию — lex.
; Счётчики — группа groebner (algo-stats 'groebner); журнал шагов — крупными шагами (record-step).

(module groebner
  (export groebner groebner-check normal-form normal-form-with-quotients ideal-certificate eliminate fglm zero-dim? groebner-lex))

; ---------- счётчики ----------
; topsteps/tailsteps — шаги редукции до первого терма, ушедшего в остаток (верх), и после него (хвост);
; ratops/coefbits/maxbits — арифметика коэффициентов (только при groebner-diag = stats | trace): ratops — число сложений
; совпавших мономов, умножений термов и делений при нормировке; coefbits — сумма длин (числитель + знаменатель, в битах)
; результатов сложений; maxbits — максимум длины результата любой из этих операций. Те же места и смысл, что в Groebner.fs.
(algo-stats-register 'groebner
  '(calls pairs product chain bk reductions zero added basis topsteps tailsteps ratops coefbits maxbits))
(define (gb-count c) (algo-count 'groebner c))
(define (gb-count-n c n) (if (> n 0) (algo-count 'groebner c n) 0))

; диагностика — переключатель groebner-diag: off | stats | trace (trace — ещё строка на каждую редукцию S-многочлена)
(algorithm-register 'groebner-diag '(off stats trace) 'off)
(define gb-stats? #f)
(define gb-trace? #f)
(define gb-clock0 0)

; учесть операцию с результатом x: ratops + 1, maxbits = max
(define (gb-note-max b)
  (let ((cur (algo-count 'groebner 'maxbits 0)))
    (if (> b cur) (algo-count 'groebner 'maxbits (- b cur)) cur)))
(define (gb-note-op x)
  (algo-count 'groebner 'ratops)
  (gb-note-max (rational-bits x)))
(define (gb-note-sum x)                          ; сложение: ещё и coefbits
  (let ((b (rational-bits x)))
    (algo-count 'groebner 'ratops)
    (algo-count 'groebner 'coefbits b)
    (gb-note-max b)))

; ---------- мономы ----------

; текущий порядок: функция сравнения мономов → -1 / 0 / 1 (устанавливается gb-set-order!)
(define gb-order 'lex)
(define gb-block 0)

(define (gb-cmp-list a b)                       ; лексикографически по спискам чисел
  (cond ((null? a) 0)
        ((< (car a) (car b)) -1)
        ((> (car a) (car b)) 1)
        (else (gb-cmp-list (cdr a) (cdr b)))))

; обратный лексикографический хвост: последний отличающийся показатель; меньший показатель → моном больше
(define (gb-revlex a b last)
  (cond ((null? a) last)
        ((< (car a) (car b)) (gb-revlex (cdr a) (cdr b) 1))
        ((> (car a) (car b)) (gb-revlex (cdr a) (cdr b) -1))
        (else (gb-revlex (cdr a) (cdr b) last))))

(define (gb-cmp-lex a b) (gb-cmp-list (cdr a) (cdr b)))
(define (gb-cmp-grlex a b) (gb-cmp-list a b))
(define (gb-cmp-grevlex a b)
  (cond ((< (car a) (car b)) -1)
        ((> (car a) (car b)) 1)
        (else (gb-revlex (cdr a) (cdr b) 0))))

; блочный порядок: степень и обратный лекс. по первым k переменным, затем — по остальным
(define (gb-sum-k l k acc) (if (= k 0) acc (gb-sum-k (cdr l) (- k 1) (+ acc (car l)))))
(define (gb-cmp-block a b)
  (let ((da (gb-sum-k (cdr a) gb-block 0)) (db (gb-sum-k (cdr b) gb-block 0)))
    (cond ((< da db) -1)
          ((> da db) 1)
          (else
           (let ((r (gb-revlex (take (cdr a) gb-block) (take (cdr b) gb-block) 0)))
             (if (not (= r 0))
                 r
                 (let ((ra (drop (cdr a) gb-block)) (rb (drop (cdr b) gb-block)))
                   (cond ((< (- (car a) da) (- (car b) db)) -1)
                         ((> (- (car a) da) (- (car b) db)) 1)
                         (else (gb-revlex ra rb 0))))))))))

(define gb-cmp gb-cmp-lex)

(define (gb-set-order! ord)
  (cond ((equal? ord 'lex) (set! gb-cmp gb-cmp-lex))
        ((equal? ord 'grlex) (set! gb-cmp gb-cmp-grlex))
        ((equal? ord 'grevlex) (set! gb-cmp gb-cmp-grevlex))
        ((and (list? ord) (= (length ord) 2) (equal? (car ord) 'block) (integer? (cadr ord)))
         (set! gb-block (cadr ord))
         (set! gb-cmp gb-cmp-block))
        (else (error "groebner: порядок — lex, grlex или grevlex, получено" ord)))
  (set! gb-order ord))

(define (gb-mmul a b) (if (null? a) '() (cons (+ (car a) (car b)) (gb-mmul (cdr a) (cdr b)))))
(define (gb-mdiv a b) (if (null? a) '() (cons (- (car a) (car b)) (gb-mdiv (cdr a) (cdr b)))))
; a делит b (покомпонентно ≤; полная степень проверяется первой — быстрый отсев)
(define (gb-mdivides? a b)
  (cond ((null? a) #t)
        ((> (car a) (car b)) #f)
        (else (gb-mdivides? (cdr a) (cdr b)))))
(define (gb-mmax a b) (if (null? a) '() (cons (max (car a) (car b)) (gb-mmax (cdr a) (cdr b)))))
(define (gb-mlcm a b)
  (let ((e (gb-mmax (cdr a) (cdr b)))) (cons (apply + e) e)))
; взаимно просты: ни одной общей переменной
(define (gb-coprime? a b)
  (cond ((null? a) #t)
        ((and (> (car a) 0) (> (car b) 0)) #f)
        (else (gb-coprime? (cdr a) (cdr b)))))
(define (gb-mcoprime? a b) (gb-coprime? (cdr a) (cdr b)))

; ---------- многочлены ----------

(define (gb-lm p) (cdr (car p)))
(define (gb-lc p) (car (car p)))
(define (gb-revapp acc l) (if (null? acc) l (gb-revapp (cdr acc) (cons (car acc) l))))

; p + q (слияние по убыванию мономов)
(define (gb-add-acc p q acc)
  (cond ((null? p) (gb-revapp acc q))
        ((null? q) (gb-revapp acc p))
        (else
         (let ((c (gb-cmp (cdr (car p)) (cdr (car q)))))
           (cond ((= c 1) (gb-add-acc (cdr p) q (cons (car p) acc)))
                 ((= c -1) (gb-add-acc p (cdr q) (cons (car q) acc)))
                 (else
                  (let ((s (+ (car (car p)) (car (car q)))))
                    (if gb-stats? (gb-note-sum s))
                    (if (= s 0)
                        (gb-add-acc (cdr p) (cdr q) acc)
                        (gb-add-acc (cdr p) (cdr q) (cons (cons s (cdr (car p))) acc))))))))))
(define (gb-add p q) (gb-add-acc p q '()))

; c·m·q (моном m, число c ≠ 0): порядок термов сохраняется (порядок мономиальный)
(define (gb-mul-term c m q)
  (if gb-stats?
      (map (lambda (t) (let ((x (* c (car t)))) (gb-note-op x) (cons x (gb-mmul m (cdr t))))) q)
      (map (lambda (t) (cons (* c (car t)) (gb-mmul m (cdr t)))) q)))

(define (gb-monic p)
  (if (null? p)
      p
      (let ((c (gb-lc p)))
        (cond ((= c 1) p)
              (gb-stats? (map (lambda (t) (let ((x (/ (car t) c))) (gb-note-op x) (cons x (cdr t)))) p))
              (else (map (lambda (t) (cons (/ (car t) c) (cdr t))) p))))))

; первый g из списка элементов (idx sugar poly), чей старший моном делит m, иначе #f
(define (gb-find-reducer m gs)
  (cond ((null? gs) #f)
        ((gb-mdivides? (gb-lm (caddr (car gs))) m) (car gs))
        (else (gb-find-reducer m (cdr gs)))))

; Полная редукция p по элементам gs (монические): (остаток . sugar). sug — sugar p; при вычитании t·g
; sugar результата = max(sugar, sugar(g) + deg t) (Giovini и др. 1991)
(define (gb-reduce-acc p sug gs acc)
  (if (null? p)
      (cons (reverse acc) sug)
      (let* ((m (cdr (car p))) (g (gb-find-reducer m gs)))
        (if g
            (let* ((gp (caddr g)) (t (gb-mdiv m (gb-lm gp))))
              (gb-count (if (null? acc) 'topsteps 'tailsteps))
              (gb-reduce-acc (gb-add (cdr p) (gb-mul-term (- (car (car p))) t (cdr gp)))
                             (max sug (+ (cadr g) (car t))) gs acc))
            (gb-reduce-acc (cdr p) sug gs (cons (car p) acc))))))
(define (gb-reduce p sug gs) (gb-reduce-acc p sug gs '()))

; нормальная форма многочлена по списку монических многочленов
(define (gb-nf p polys)
  (car (gb-reduce p 0 (map (lambda (q) (list 0 0 q)) polys))))

; S-многочлен монических f, g (старшие термы сокращаются — сразу берутся хвосты)
(define (gb-spoly f g)
  (let ((L (gb-mlcm (gb-lm f) (gb-lm g))))
    (gb-add (gb-mul-term 1 (gb-mdiv L (gb-lm f)) (cdr f))
            (gb-mul-term -1 (gb-mdiv L (gb-lm g)) (cdr g)))))

; ---------- выражение ↔ многочлен ----------

(define (gb-zeros n) (if (= n 0) '() (cons 0 (gb-zeros (- n 1)))))
(define (gb-add-at l i k) (if (= i 0) (cons (+ (car l) k) (cdr l)) (cons (car l) (gb-add-at (cdr l) (- i 1) k))))
(define (gb-index x vars i)
  (cond ((null? vars) #f) ((equal? (car vars) x) i) (else (gb-index x (cdr vars) (+ i 1)))))

; множитель терма → (коэффициент . показатели)
(define (gb-factor f vars acc)
  (cond ((rational-number? f) (cons (* (car acc) f) (cdr acc)))
        ((and (symbol? f) (gb-index f vars 0))
         (cons (car acc) (gb-add-at (cdr acc) (gb-index f vars 0) 1)))
        ((and (op-expr? f) (equal? (car f) '^) (symbol? (cadr f)) (gb-index (cadr f) vars 0)
              (integer? (caddr f)) (> (caddr f) 0))
         (cons (car acc) (gb-add-at (cdr acc) (gb-index (cadr f) vars 0) (caddr f))))
        (else (error (string-append "groebner: не многочлен от " (to-string vars)
                                    " с рациональными коэффициентами: множитель " (math-print f))))))

(define (gb-term t vars)
  (let ((r (foldl (lambda (acc f) (gb-factor f vars acc)) (cons 1 (gb-zeros (length vars)))
                  (if (and (op-expr? t) (equal? (car t) '*)) (cdr t) (list t)))))
    (cons (car r) (cons (apply + (cdr r)) (cdr r)))))

(define (gb-term> a b) (= (gb-cmp (cdr a) (cdr b)) 1))

(define (gb-equation->expr e)
  (if (and (op-expr? e) (equal? (car e) '=)) (list '- (cadr e) (caddr e)) e))

; выражение → многочлен (в текущем порядке); подобные термы expand уже собрал
(define (gb-from-expr e vars)
  (let ((x (expand (gb-equation->expr e))))
    (cond ((equal? x 0) '())
          ((and (op-expr? x) (equal? (car x) '+))
           (sort (filter (lambda (t) (not (= (car t) 0))) (map (lambda (t) (gb-term t vars)) (cdr x))) gb-term>))
          (else (list (gb-term x vars))))))

(define (gb-term->expr t vars)
  (cons '* (cons (car t) (map2 (lambda (v k) (list '^ v k)) vars (cdr (cdr t))))))
(define (gb-to-expr p vars)
  (if (null? p) 0 (simplify (cons '+ (map (lambda (t) (gb-term->expr t vars)) p)))))

; ---------- Бухбергер ----------
; Элемент базиса — (номер sugar многочлен); пара — (lcm sugar a b), a, b — элементы.

(define gb-next-id 0)
(define gb-max-reductions 20000)                 ; защита от «вечного» счёта (ошибка, а не зависание)
; стратегия выбора пар — переключатель groebner-strategy: normal (минимум lcm в порядке, по умолчанию) | sugar (минимум
; sugar, затем lcm); (set-algorithm 'groebner-strategy 'sugar), среда LISP_GROEBNER_STRATEGY
(algorithm-register 'groebner-strategy '(normal sugar) 'normal)
(define gb-strategy 'normal)

(define (gb-element p sug)
  (set! gb-next-id (+ gb-next-id 1))
  (list gb-next-id sug p))
(define (gb-elm e) (gb-lm (caddr e)))
(define (gb-same? a b) (= (car a) (car b)))

(define (gb-pair a b)
  (let* ((ma (gb-elm a)) (mb (gb-elm b)) (L (gb-mlcm ma mb)))
    (list L (max (+ (cadr a) (- (car L) (car ma))) (+ (cadr b) (- (car L) (car mb)))) a b)))

; пара p «лучше» q по стратегии
(define (gb-pair< p q)
  (if (equal? gb-strategy 'sugar)
      (or (< (cadr p) (cadr q))
          (and (= (cadr p) (cadr q)) (= (gb-cmp (car p) (car q)) -1)))
      (= (gb-cmp (car p) (car q)) -1)))

; выбор пары: (лучшая . остальные)
(define (gb-select ps)
  (let ((best (foldl (lambda (b p) (if (gb-pair< p b) p b)) (car ps) (cdr ps))))
    (cons best (gb-remove-first best ps))))
(define (gb-remove-first x l)
  (if (eq-pair? x (car l)) (cdr l) (cons (car l) (gb-remove-first x (cdr l)))))
(define (eq-pair? p q) (and (gb-same? (caddr p) (caddr q)) (gb-same? (nth p 3) (nth q 3))))

; вставка элемента в список по возрастанию старших мономов (делители — от маленьких: CLO, с. 111)
(define (gb-insert e gs)
  (cond ((null? gs) (list e))
        ((= (gb-cmp (gb-elm e) (gb-elm (car gs))) -1) (cons e gs))
        (else (cons (car gs) (gb-insert e (cdr gs))))))

; update(G, B, h) — BW с. 230 (критерии Гебауэра–Мёллера); → (G' . B')
(define (gb-update gs bs h)
  (let* ((mh (gb-elm h))
         ; новые пары (h, g): отбросить, если lcm другой новой пары (ещё не рассмотренной или принятой) делит lcm(h, g);
         ; пары с взаимно простыми старшими мономами принимаются (участвуют в отсеве), затем удаляются.
         ; lcm(h, g) считается один раз: список (lcm . g)
         (D (gb-new-pairs h mh (map (lambda (g) (cons (gb-mlcm mh (gb-elm g)) g)) gs) '()))
         (E (filter (lambda (pr) (not (gb-mcoprime? mh (gb-elm (nth pr 3))))) D))
         ; старые пары (g1, g2): B_k — lm(h) | lcm(g1, g2), и lcm с h у обоих отличен от lcm(g1, g2)
         (B2 (filter (lambda (pr)
                       (let ((L (car pr)))
                         (or (not (gb-mdivides? mh L))
                             (equal? (gb-mlcm (gb-elm (caddr pr)) mh) L)
                             (equal? (gb-mlcm (gb-elm (nth pr 3)) mh) L))))
                     bs))
         (G2 (gb-insert h (filter (lambda (g) (not (gb-mdivides? mh (gb-elm g)))) gs))))
    (gb-count-n 'product (- (length D) (length E)))
    (gb-count-n 'chain (- (length gs) (length D)))
    (gb-count-n 'bk (- (length bs) (length B2)))
    (gb-count-n 'pairs (length E))
    (cons G2 (append B2 E))))

; C — оставшиеся кандидаты (lcm . g), D — принятые пары (lcm sugar h g)
(define (gb-new-pairs h mh C D)
  (if (null? C)
      D
      (let* ((L (car (car C))) (g (cdr (car C))) (rest (cdr C)))
        (if (or (gb-mcoprime? mh (gb-elm g))
                (and (not (any? (lambda (c) (gb-mdivides? (car c) L)) rest))
                     (not (any? (lambda (pr) (gb-mdivides? (car pr) L)) D))))
            (gb-new-pairs h mh rest (cons (gb-pair h g) D))
            (gb-new-pairs h mh rest D)))))

; начальная интерредукция (BW с. 203): каждый многочлен — по предыдущим, до неподвижной точки
(define (gb-interreduce-pass fs done acc)
  (if (null? fs)
      (reverse acc)
      (let ((r (gb-monic (gb-nf (car fs) done))))
        (gb-interreduce-pass (cdr fs) (cons (car fs) done) (if (null? r) acc (cons r acc))))))
(define (gb-interreduce fs)
  (let ((f1 (gb-interreduce-pass fs '() '())))
    (if (equal? f1 fs) fs (gb-interreduce f1))))

; полная степень многочлена (sugar образующей)
(define (gb-tdeg p) (apply max (map cadr p)))
(define (gb-constant? p) (= (car (gb-lm p)) 0))

; базис Грёбнера (минимальный, не приведённый): список элементов
(define (gb-buchberger fs)
  (let* ((f0 (gb-interreduce (map gb-monic fs)))
         (sorted (sort f0 (lambda (a b) (= (gb-cmp (gb-lm a) (gb-lm b)) -1)))))
    (if (any? gb-constant? f0)
        (list (gb-element (list (cons 1 (gb-lm (car (filter gb-constant? f0))))) 0))
        (let ((st (foldl (lambda (st p)
                           (gb-update (car st) (cdr st) (gb-element p (gb-tdeg p))))
                         (cons '() '()) sorted)))
          (gb-loop (car st) (cdr st) 0)))))

; строка трассы (как в Groebner.fs; там — stderr): номер, |G|, |B| (до выбора пары), членов S-многочлена и остатка,
; maxbits, время с начала счёта (мкс)
(define (gb-trace-line n G B sp rem)
  (display (string-append "groebner #" (to-string n) " |G|=" (to-string (length G)) " |B|="(to-string (length B))
                          " S=" (to-string (length sp)) " rem=" (to-string (length rem))
                          " maxbits=" (to-string (algo-count 'groebner 'maxbits 0))
                          " t=" (to-string (- (clock-us) gb-clock0)) " мкс"))
  (newline))

; главный цикл: пока есть пары — выбрать, S-многочлен, редукция по G (по возрастанию lm), ненулевой — в базис
(define (gb-loop G B n)
  (cond ((null? B) G)
        ((> n gb-max-reductions)
         (error "groebner: превышен предел числа редукций S-многочленов" gb-max-reductions))
        (else
         (let* ((sel (gb-select B)) (pr (car sel)) (B1 (cdr sel))
                (sp (gb-spoly (caddr (caddr pr)) (caddr (nth pr 3))))
                (r (gb-reduce sp (cadr pr) G))
                (h (begin
                     (if gb-trace? (gb-trace-line (+ n 1) G B sp (car r)))
                     (gb-monic (car r)))))
           (gb-count 'reductions)
           (cond ((null? h) (gb-count 'zero) (gb-loop G B1 (+ n 1)))
                 ((gb-constant? h)
                  (gb-count 'added)
                  (list (gb-element h 0)))               ; единичный идеал — дальше считать нечего
                 (else
                  (gb-count 'added)
                  (let ((st (gb-update G B1 (gb-element h (cdr r)))))
                    (gb-loop (car st) (cdr st) (+ n 1)))))))))

; приведённый базис: каждый элемент минимального базиса — по остальным (хвосты), монический; по убыванию lm
(define (gb-reduced G)
  (let ((ps (map (lambda (g)
                   (gb-monic (car (gb-reduce (caddr g) 0 (filter (lambda (x) (not (gb-same? x g))) G)))))
                 G)))
    (sort (filter (lambda (p) (not (null? p))) ps)
          (lambda (a b) (= (gb-cmp (gb-lm a) (gb-lm b)) 1)))))

; приведённый базис Грёбнера (внутреннее представление) многочленов fs (внутреннее представление)
; Реализация — переключатель groebner: fsharp (Groebner.fs, по умолчанию) | lisp (этот файл — эталон; тот же алгоритм,
; базисы и счётчики совпадают); (set-algorithm 'groebner 'lisp), среда LISP_GROEBNER
(define (gb-basis fs)
  (set! gb-strategy (algorithm 'groebner-strategy))
  (set! gb-stats? (not (equal? (algorithm 'groebner-diag) 'off)))
  (set! gb-trace? (equal? (algorithm 'groebner-diag) 'trace))
  (set! gb-clock0 (clock-us))
  (let ((nz (filter (lambda (p) (not (null? p))) fs)))
    (cond ((null? nz) '())
          ((equal? (algorithm 'groebner) 'fsharp) (groebner-basis-raw nz gb-order gb-strategy gb-max-reductions))
          (else (gb-reduced (gb-buchberger nz))))))

; ---------- проверки (для тестов) ----------

; все S-многочлены редуцируются к нулю (критерий Бухбергера) — по образующим ps (монические)
(define (gb-groebner? ps)
  (let ((ms (map gb-monic ps)))
    (every? (lambda (i)
              (every? (lambda (j) (null? (gb-nf (gb-spoly (nth ms i) (nth ms j)) ms)))
                      (filter (lambda (j) (> j i)) (range (length ms)))))
            (range (length ms)))))

; приведённость: монические, ни один терм не делится на старший моном другого
(define (gb-reduced? ps)
  (every? (lambda (p)
            (and (= (gb-lc p) 1)
                 (every? (lambda (q)
                           (or (equal? p q)
                               (not (any? (lambda (t) (gb-mdivides? (gb-lm q) (cdr t))) p))))
                         ps)))
          ps))

; ---------- API ----------

(define (gb-check-vars vars who)
  (if (not (and (list? vars) (not (null? vars)) (every? symbol? vars)))
      (error (string-append who ": переменные — непустой список символов, получено") vars)))

; выполнить thunk с порядком ord (прежний порядок восстанавливается)
(define (gb-with-order ord thunk)
  (let ((old gb-order) (old-block gb-block))
    (gb-set-order! ord)
    (unwind-protect (thunk)
      (set! gb-block old-block)
      (gb-set-order! old))))

(define (gb-opt-order opt) (if (null? opt) 'lex (car opt)))

(define (gb-record-basis fs vars G)
  (if (step-log-enabled?)
      (record-step 'groebner-basis "Базис Грёбнера"
                   (string-append "алгоритм Бухбергера, порядок " (to-string gb-order) ", переменные "
                                  (to-string vars) "; элементов базиса: " (to-string (length G)))
                   (cons 'list fs) (cons 'list G))))

; (groebner многочлены переменные [порядок]) → приведённый базис (список выражений, по убыванию старших мономов)
(define (groebner fs vars &rest opt)
  (gb-check-vars vars "groebner")
  (gb-count 'calls)
  (gb-with-order (gb-opt-order opt)
    (lambda ()
      (let* ((ps (map (lambda (e) (gb-from-expr e vars)) fs))
             (G (map (lambda (p) (gb-to-expr p vars)) (gb-basis ps))))
        (gb-count-n 'basis (length G))
        (gb-record-basis fs vars G)
        G))))

; символы f, не входящие в vars (становятся младшими переменными normal-form)
(define (gb-extra-symbols e vars)
  (filter (lambda (v) (and (symbol? v) (not (member? v vars)))) (variables (expand (gb-equation->expr e)))))

; (normal-form f образующие переменные [порядок]) — остаток f по модулю идеала образующих (единственный: делится
; на приведённый базис); символы f вне списка переменных — младшие переменные (коэффициенты-параметры)
(define (normal-form f gens vars &rest opt)
  (gb-check-vars vars "normal-form")
  (let ((all (append vars (gb-extra-symbols f vars))))
    (gb-with-order (gb-opt-order opt)
      (lambda ()
        (let* ((G (gb-basis (map (lambda (e) (gb-from-expr e vars)) gens)))
               (Gx (map (lambda (p) (gb-widen p (- (length all) (length vars)))) G))
               (r (gb-to-expr (gb-nf (gb-from-expr f all) Gx) all)))
          (if (step-log-enabled?)
              (record-step 'normal-form "Нормальная форма" "остаток от деления на приведённый базис Грёбнера" f r))
          r)))))

; ---------- деление с частными (сертификаты идеала) ----------

; первый индекс i, для которого старший моном gs[i] делит m, иначе #f
(define (gb-q-find m gs i)
  (cond ((null? gs) #f)
        ((and (not (null? (car gs))) (gb-mdivides? (gb-lm (car gs)) m)) i)
        (else (gb-q-find m (cdr gs) (+ i 1)))))

(define (gb-q-bump qs i term)
  (if (= i 0)
      (cons (gb-add (car qs) (list term)) (cdr qs))
      (cons (car qs) (gb-q-bump (cdr qs) (- i 1) term))))

; полное деление p на gs (любые, не обязательно монические): (остаток . частные); p = Σ q_i g_i + r
(define (gb-q-divide p gs qs acc)
  (if (null? p)
      (cons (reverse acc) qs)
      (let* ((lt (car p)) (m (cdr lt)) (i (gb-q-find m gs 0)))
        (if i
            (let* ((g (nth gs i))
                   (c (/ (car lt) (gb-lc g)))
                   (t (gb-mdiv m (gb-lm g))))
              (gb-q-divide (gb-add (cdr p) (gb-mul-term (- c) t (cdr g)))
                           gs (gb-q-bump qs i (cons c t)) acc))
            (gb-q-divide (cdr p) gs qs (cons lt acc))))))

; (normal-form-with-quotients f gs vars [порядок]) → (r (q1 … qk)): f = Σ qi·gi + r, ни один моном r не делится
; на старшие мономы gi. gs делятся как есть (не базис Грёбнера — остаток не обязан быть 0 для элементов идеала)
(define (normal-form-with-quotients f gs vars &rest opt)
  (gb-check-vars vars "normal-form-with-quotients")
  (let ((all (append vars (gb-extra-symbols f vars))))
    (gb-with-order (gb-opt-order opt)
      (lambda ()
        (let* ((ps (map (lambda (e) (gb-from-expr e all)) gs))
               (res (gb-q-divide (gb-from-expr f all) ps (map (lambda (g) '()) ps) '())))
          (list (gb-to-expr (car res) all)
                (map (lambda (q) (gb-to-expr q all)) (cdr res))))))))

; (ideal-certificate f gs vars [порядок]) → (q1 … qk) с f = Σ qi·gi, если деление даёт нулевой остаток, иначе #f.
; Равенство Σ qi·gi − f = 0 проверяется (expand); при нарушении — #f
(define (ideal-certificate f gs vars &rest opt)
  (let ((res (if (null? opt)
                 (normal-form-with-quotients f gs vars)
                 (normal-form-with-quotients f gs vars (car opt)))))
    (if (and (equal? (car res) 0)
             (equal? (expand (list '- (cons '+ (cons 0 (map2 (lambda (q g) (list '* q (gb-equation->expr g)))
                                                              (cadr res) gs)))
                                   (gb-equation->expr f)))
                     0))
        (cadr res)
        #f)))

; (groebner-check многочлены базис переменные [порядок]) → ((f остаток) ...): остаток каждого исходного многочлена
; (уравнение a = b — разность) от деления на базис; все остатки 0 ⇔ идеал исходных многочленов вложен в идеал базиса
; (обратное вложение — базис ⊂ идеала исходных — здесь не проверяется). Шаг 22.6: сертификат ideal_membership
(define (groebner-check fs G vars &rest opt)
  (map (lambda (f)
         (list f (if (null? opt)
                     (normal-form (gb-equation->expr f) G vars)
                     (normal-form (gb-equation->expr f) G vars (car opt)))))
       fs))

; дополнить мономы нулевыми показателями k новых (младших) переменных
(define (gb-widen p k)
  (if (= k 0) p (map (lambda (t) (append t (gb-zeros k))) p)))

; ---------- FGLM: перевод базиса нульмерного идеала в другой порядок ----------
; Faugère–Gianni–Lazard–Mora (1993). Идеал нульмерный ⇔ факторкольцо ℚ[x]/I — конечномерное векторное пространство;
; базис — стандартные мономы (не делящиеся на старшие мономы исходного базиса), размерность N. Мономы обходятся по
; ВОЗРАСТАНИЮ в целевом порядке (очередь кандидатов; начиная с 1, потомки — произведения на переменные). Для каждого
; монома m (не делящегося на уже найденные старшие мономы нового базиса) берётся нормальная форма NF(m) в исходном
; порядке — вектор длины N; NF(x_i·m') = NF(x_i·NF(m')) считается из NF родителя m' = m/x_i, поэтому по высоким
; степеням ничего не редуцируется. Если вектор линейно зависит от уже принятых — найдено соотношение
; m + Σ c_k m_k = 0, т. е. очередной элемент нового базиса (старший моном m — наибольший в целевом порядке, хвост —
; принятые мономы, элемент монический и приведённый); иначе m — новый «стандартный моном» нового порядка, и в очередь
; ставятся его кратные. Зависимость ищется ступенчатым видом над ℚ; к каждому вектору приписывается единичный вектор
; (какой моном), и сведённая к нулю строка выдаёт коэффициенты соотношения. Ровно N мономов принимается, обход конечен.

(define gb-fg-G '())      ; исходный базис (монический, внутреннее представление, порядок «из»)
(define gb-fg-n 0)        ; число переменных
(define gb-fg-N 0)        ; размерность факторкольца
(define gb-fg-cmp gb-cmp-lex)
(define gb-fg-units '())  ; мономы переменных (1 0 .. 1 .. 0)

(define (gb-fg-cmp-of ord)
  (cond ((equal? ord 'lex) gb-cmp-lex)
        ((equal? ord 'grlex) gb-cmp-grlex)
        ((equal? ord 'grevlex) gb-cmp-grevlex)
        (else (error "fglm: целевой порядок — lex, grlex или grevlex, получено" ord))))

(define (gb-fg-units-of n)
  (map (lambda (i) (cons 1 (gb-add-at (gb-zeros n) i 1))) (range n)))

; у каждой переменной среди старших мономов есть чистая степень (и базис непуст)
(define (gb-fg-zero-dim? lms n)
  (and (not (null? lms))
       (every? (lambda (i)
                 (any? (lambda (m) (and (> (car m) 0) (= (car m) (nth (cdr m) i)))) lms))
               (range n))))

(define (gb-fg-divisible? x lms) (any? (lambda (l) (gb-mdivides? l x)) lms))

; стандартные мономы: обход в ширину от 1
(define (gb-fg-std queue acc lms)
  (if (null? queue)
      (reverse acc)
      (let* ((m (car queue))
             (new (filter (lambda (x) (and (not (gb-fg-divisible? x lms)) (not (member? x acc))
                                           (not (member? x queue))))
                          (map (lambda (u) (gb-mmul m u)) gb-fg-units))))
        (gb-fg-std (append (cdr queue) new) (cons m acc) lms))))

(define (gb-fg-coef p m)
  (cond ((null? p) 0) ((equal? (cdr (car p)) m) (car (car p))) (else (gb-fg-coef (cdr p) m))))

(define (gb-fg-lookup m alist)
  (cond ((null? alist) #f) ((equal? (car (car alist)) m) (cdr (car alist))) (else (gb-fg-lookup m (cdr alist)))))

; нормальная форма монома m (внутренний многочлен): из NF родителя m / x_i
(define (gb-fg-nf m stairs)
  (if (= (car m) 0)
      (list (cons 1 m))
      (let* ((i (car (filter (lambda (j) (> (nth (cdr m) j) 0)) (range gb-fg-n))))
             (u (nth gb-fg-units i))
             (parent (gb-fg-lookup (gb-mdiv m u) stairs)))
        (gb-nf (gb-mul-term 1 u parent) gb-fg-G))))

; вектор координат NF по стандартным мономам, длиной N, затем единичный вектор позиции k длиной N + 1
; (k = N — последний, уже зависимый моном)
(define (gb-fg-vector nf std k)
  (append (map (lambda (s) (gb-fg-coef nf s)) std)
          (append (gb-zeros k) (cons 1 (gb-zeros (- gb-fg-N k))))))

; свести v по строкам (pivot . строка) в порядке добавления
(define (gb-fg-sweep v rows)
  (if (null? rows)
      v
      (let ((a (nth v (car (car rows)))))
        (gb-fg-sweep (if (= a 0) v (map2 (lambda (x y) (- x (* a y))) v (cdr (car rows)))) (cdr rows)))))

(define (gb-fg-pivot v i)                       ; первый ненулевой среди первых N, иначе #f
  (cond ((= i gb-fg-N) #f) ((not (= (nth v i) 0)) i) (else (gb-fg-pivot v (+ i 1)))))

(define (gb-fg-enqueue x q)                     ; вставка в очередь по возрастанию целевого порядка, без повторов
  (if (null? q)
      (list x)
      (let ((c (gb-fg-cmp x (car q))))
        (cond ((= c 0) q) ((= c -1) (cons x q)) (else (cons (car q) (gb-fg-enqueue x (cdr q))))))))

(define (gb-fg-enqueue-all xs q) (if (null? xs) q (gb-fg-enqueue-all (cdr xs) (gb-fg-enqueue (car xs) q))))

; очередь, принятые (моном . NF) в порядке принятия, строки, найденные старшие мономы, найденные (моном . коэффициенты)
(define (gb-fg-loop queue stairs rows lms out std)
  (if (null? queue)
      out
      (let ((m (car queue)))
        (if (gb-fg-divisible? m lms)
            (gb-fg-loop (cdr queue) stairs rows lms out std)
            (let* ((k (length stairs))
                   (nf (gb-fg-nf m stairs))
                   (v (gb-fg-sweep (gb-fg-vector nf std k) rows))
                   (p (gb-fg-pivot v 0)))
              (if p
                  (let ((row (map (lambda (x) (/ x (nth v p))) v)))
                    (gb-fg-loop (gb-fg-enqueue-all (filter (lambda (x) (not (gb-fg-divisible? x lms)))
                                                           (map (lambda (u) (gb-mmul m u)) gb-fg-units))
                                                   (cdr queue))
                                (append stairs (list (cons m nf))) (append rows (list (cons p row))) lms out std))
                  (gb-fg-loop (cdr queue) stairs rows (cons m lms)
                              (cons (gb-fg-poly (cons m (take (drop v gb-fg-N) k)) stairs) out) std)))))))

; найденное соотношение → многочлен: m + Σ c_k m_k, термы по убыванию в целевом порядке
(define (gb-fg-poly rel stairs)
  (let ((tail (filter (lambda (t) (not (= (car t) 0)))
                      (map2 (lambda (c s) (cons c (car s))) (cdr rel) stairs))))
    (cons (cons 1 (car rel))
          (sort tail (lambda (a b) (= (gb-fg-cmp (cdr a) (cdr b)) 1))))))

; внутренний многочлен по выражению в порядке «из» (вызывать внутри gb-with-order)
(define (gb-fg-parse G vars) (map (lambda (e) (gb-monic (gb-from-expr e vars))) G))

(define (gb-fg-lms ps) (map gb-lm (filter (lambda (p) (not (null? p))) ps)))

; (zero-dim? базис переменные [порядок]) — #t, если приведённый базис Грёбнера задаёт нульмерный идеал
; (у каждой переменной есть чистая степень среди старших мономов; базис (1) — пустое множество решений — тоже #t)
(define (zero-dim? G vars &rest opt)
  (gb-check-vars vars "zero-dim?")
  (gb-with-order (gb-opt-order opt)
    (lambda ()
      (let ((ps (filter (lambda (p) (not (null? p))) (gb-fg-parse G vars))))
        (or (and (not (null? ps)) (any? gb-constant? ps))
            (gb-fg-zero-dim? (gb-fg-lms ps) (length vars)))))))

; (fglm базис переменные из-порядка в-порядок) — базис Грёбнера нульмерного идеала из порядка «из-порядка» в «в-порядок»
; (lex, grlex, grevlex; «из» — любой порядок groebner). Вход — приведённый (или хотя бы любой) базис Грёбнера в «из-порядке»
; (проверка Бухбергера не делается). Не нульмерный идеал — ошибка. Выход — приведённый базис в «в-порядке», по убыванию lm.
(define (fglm G vars from to)
  (gb-check-vars vars "fglm")
  (let ((cmp (gb-fg-cmp-of to)) (n (length vars)))
    (gb-with-order from
      (lambda ()
        (let* ((ps (gb-fg-parse G vars)) (lms (gb-fg-lms ps)))
          (cond ((and (not (null? ps)) (any? gb-constant? ps)) '(1))
                ((not (gb-fg-zero-dim? lms n))
                 (error (string-append "fglm: идеал не нульмерный (базис " (to-string G)
                                       "): у каждой переменной из " (to-string vars) " должна быть чистая степень среди старших мономов")))
                (else
                 (set! gb-fg-G (filter (lambda (p) (not (null? p))) ps))
                 (set! gb-fg-n n)
                 (set! gb-fg-cmp cmp)
                 (set! gb-fg-units (gb-fg-units-of n))
                 (let* ((std (gb-fg-std (list (cons 0 (gb-zeros n))) '() lms)))
                   (set! gb-fg-N (length std))
                   (let ((res (map (lambda (p) (gb-to-expr p vars))
                                   (gb-fg-loop (list (cons 0 (gb-zeros n))) '() '() '() '() std))))
                     (if (step-log-enabled?)
                         (record-step 'fglm "Смена порядка мономов (FGLM)"
                                      (string-append "перевод базиса нульмерного идеала из порядка " (to-string from)
                                                     " в " (to-string to) " (размерность факторкольца " (to-string gb-fg-N) ")")
                                      (cons 'list G) (cons 'list res)))
                     res)))))))))

; (groebner-lex многочлены переменные) — приведённый lex-базис: для нульмерного идеала — базис в grevlex и FGLM → lex
; (на порядки быстрее прямого lex), иначе — прямой lex (groebner ... 'lex)
(define (groebner-lex fs vars)
  (gb-check-vars vars "groebner-lex")
  (let ((G (groebner fs vars 'grevlex)))
    (if (zero-dim? G vars 'grevlex)
        (fglm G vars 'grevlex 'lex)
        (groebner fs vars 'lex))))

; (eliminate многочлены исключаемые остальные) → образующие I ∩ ℚ[остальные]: элементы базиса Грёбнера
; в блочном порядке (исключаемые ≫ остальные; внутри блоков — grevlex), не содержащие исключаемых переменных
(define (eliminate fs elim rest)
  (gb-check-vars elim "eliminate")
  (if (not (and (list? rest) (every? symbol? rest)))
      (error "eliminate: остальные переменные — список символов, получено" rest))
  (let* ((vars (append elim rest)) (k (length elim)))
    (gb-with-order (list 'block k)
      (lambda ()
        (let* ((G (gb-basis (map (lambda (e) (gb-from-expr e vars)) fs)))
               (H (filter (lambda (p) (= (gb-sum-k (cdr (gb-lm p)) k 0) 0)) G))
               (r (map (lambda (p) (gb-to-expr p vars)) H)))
          (gb-count 'calls)
          (if (step-log-enabled?)
              (record-step 'elimination "Исключение переменных"
                           (string-append "базис Грёбнера в блочном порядке, исключаются " (to-string elim))
                           (cons 'list fs) (cons 'list r)))
          r)))))
