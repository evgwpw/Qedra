; units.lisp — величины с единицами, перевод и проверка размерности (шаг DIM.1).
;
; Размерность — список из 7 рациональных показателей над базовыми величинами СИ в порядке
; (L M T I Θ N J): длина, масса, время, ток, температура, количество вещества, сила света.
; Единица — выражение над символами единиц: m, kg, (* kg (^ m 2) (^ s -2)), (/ km h), (^ s -1).
; Таблица: (множитель-к-СИ . размерность); множители точные (дроби): 1 eV = 1602176634/10^28 Дж,
; 1 mile = 1609344/1000 м. Масса: базовая единица kg, в таблице g = 1/1000, приставка k даёт kg.
; Приставки СИ (одна буква: T G M k h c d m μ u n p) применяются к единицам с признаком «prefixable»;
; сначала ищется точное имя (min — минута, а не милли-ин; h — час; T — тесла; cd — кандела).
; Температура: K — единица размерности Θ; °C/°F (и degC/degF) — только в convert-temperature
; (аффинный перевод), в мультипликативных выражениях они не допускаются.
; Величина — (quantity значение единица).
; dimension-check: формула над символами с env ((имя . единица-или-размерность) …) → (ok d)
; или (mismatch где d1 d2): где — подвыражение; для exp/log/sin… d2 = нулевая размерность,
; для нерационального показателя при размерной основе d2 = символ rational-exponent.
; Показатели степени — только рациональные числа; sqrt = ^1/2. Константы pi, %i, %e — без размерности.
; Шаг DIM.2 (π-теорема Бэкингема): dimension-matrix, pi-groups (с :repeating), pi-groups-check
; (сертификат), dimensional-solve. Линейная алгебра над ℚ — собственный RREF (un-rref).

(module units
  (export quantity quantity? quantity-value quantity-unit
          unit-dimension unit-factor same-dimension? dimension->string
          convert convert-temperature
          quantity-add quantity-mul quantity-div quantity-pow
          dimension-check
          dimension-matrix pi-groups pi-groups-check dimensional-solve))

  (define un-names '("L" "M" "T" "I" "Θ" "N" "J"))
  (define un-zero '(0 0 0 0 0 0 0))

  (define (un-dim-add a b) (map2 + a b))
  (define (un-dim-scale a k) (map (lambda (e) (* e k)) a))

  ; степень точной дроби с целым показателем (^ даёт дробь не во всех случаях)
  (define (un-ipow f n)
    (if (< n 0)
        (/ 1 (un-ipow f (- n)))
        (let loop ((i 0) (acc 1))
          (if (= i n) acc (loop (+ i 1) (* acc f))))))

  (define (un-rpow f k)
    (cond ((integer? k) (un-ipow f k))
          ((= f 1) 1)
          (else (error "units: нерациональный множитель при дробной степени:" f k))))

  (define (un-float? x) (equal? (type-of x) 'float))
  (define (un-rational-exp? k) (and (number? k) (not (un-float? k))))

  ; запись таблицы: (имя множитель размерность prefixable)
  (define un-table
    (list
     (list 'm 1 '(1 0 0 0 0 0 0) #t) (list 'g 1/1000 '(0 1 0 0 0 0 0) #t)
     (list 's 1 '(0 0 1 0 0 0 0) #t) (list 'A 1 '(0 0 0 1 0 0 0) #t)
     (list 'K 1 '(0 0 0 0 1 0 0) #t) (list 'mol 1 '(0 0 0 0 0 1 0) #t)
     (list 'cd 1 '(0 0 0 0 0 0 1) #t)
     (list 'N 1 '(1 1 -2 0 0 0 0) #t) (list 'J 1 '(2 1 -2 0 0 0 0) #t)
     (list 'W 1 '(2 1 -3 0 0 0 0) #t) (list 'Pa 1 '(-1 1 -2 0 0 0 0) #t)
     (list 'Hz 1 '(0 0 -1 0 0 0 0) #t) (list 'C 1 '(0 0 1 1 0 0 0) #t)
     (list 'V 1 '(2 1 -3 -1 0 0 0) #t) (list 'Ω 1 '(2 1 -3 -2 0 0 0) #t)
     (list 'ohm 1 '(2 1 -3 -2 0 0 0) #t) (list 'S 1 '(-2 -1 3 2 0 0 0) #t)
     (list 'F 1 '(-2 -1 4 2 0 0 0) #t) (list 'T 1 '(0 1 -2 -1 0 0 0) #t)
     (list 'Wb 1 '(2 1 -2 -1 0 0 0) #t) (list 'H 1 '(2 1 -2 -2 0 0 0) #t)
     (list 'lx 1 '(-2 0 0 0 0 0 1) #t) (list 'Bq 1 '(0 0 -1 0 0 0 0) #t)
     (list 'Gy 1 '(2 0 -2 0 0 0 0) #t) (list 'Sv 1 '(2 0 -2 0 0 0 0) #t)
     (list 'kat 1 '(0 0 -1 0 0 1 0) #t)
     (list 'rad 1 un-zero #f) (list 'sr 1 un-zero #f)
     (list 'min 60 '(0 0 1 0 0 0 0) #f) (list 'h 3600 '(0 0 1 0 0 0 0) #f)
     (list 'day 86400 '(0 0 1 0 0 0 0) #f)
     (list 'L 1/1000 '(3 0 0 0 0 0 0) #t)
     (list 'eV (/ 1602176634 (un-ipow 10 28)) '(2 1 -2 0 0 0 0) #t)
     (list 'cal 4184/1000 '(2 1 -2 0 0 0 0) #t)
     (list 'atm 101325 '(-1 1 -2 0 0 0 0) #f)
     (list 'bar 100000 '(-1 1 -2 0 0 0 0) #t)
     (list 'mmHg 133322387415/1000000000 '(-1 1 -2 0 0 0 0) #f)
     (list 'Torr 101325/760 '(-1 1 -2 0 0 0 0) #f)
     (list 'inch 254/10000 '(1 0 0 0 0 0 0) #f) (list 'ft 3048/10000 '(1 0 0 0 0 0 0) #f)
     (list 'mile 1609344/1000 '(1 0 0 0 0 0 0) #f)
     (list 'lb 45359237/100000000 '(0 1 0 0 0 0 0) #f)))

  (define un-prefixes
    (list (cons "T" (un-ipow 10 12)) (cons "G" (un-ipow 10 9)) (cons "M" (un-ipow 10 6))
          (cons "k" 1000) (cons "h" 100) (cons "c" 1/100) (cons "d" 1/10) (cons "m" 1/1000)
          (cons "μ" 1/1000000) (cons "u" 1/1000000) (cons "n" 1/1000000000)
          (cons "p" (/ 1 (un-ipow 10 12)))))

  ; символ единицы → (множитель . размерность)
  (define (un-lookup s)
    (let ((e (assoc s un-table)))
      (if e
          (cons (cadr e) (caddr e))
          (let* ((name (symbol->string s)) (n (string-length name))
                 (p (if (> n 1) (assoc (substring name 0 1) un-prefixes) #f))
                 (b (if p (assoc (string->symbol (substring name 1 n)) un-table) #f)))
            (if (and b (nth b 3))
                (cons (* (cdr p) (cadr b)) (caddr b))
                (error "units: неизвестная единица" s))))))

  ; единица-выражение → (множитель . размерность)
  (define (un-eval u)
    (cond ((number? u)
           (if (un-float? u)
               (error "units: множитель единицы должен быть точным числом" u)
               (cons u un-zero)))
          ((symbol? u) (un-lookup u))
          ((and (pair? u) (equal? (car u) '*))
           (foldl (lambda (acc x)
                    (let ((v (un-eval x)))
                      (cons (* (car acc) (car v)) (un-dim-add (cdr acc) (cdr v)))))
                  (cons 1 un-zero) (cdr u)))
          ((and (pair? u) (equal? (car u) '/) (pair? (cdr u)))
           (let ((first (un-eval (cadr u))))
             (foldl (lambda (acc x)
                      (let ((v (un-eval x)))
                        (cons (/ (car acc) (car v))
                              (un-dim-add (cdr acc) (un-dim-scale (cdr v) -1)))))
                    (if (null? (cddr u))
                        (cons (/ 1 (car first)) (un-dim-scale (cdr first) -1))
                        first)
                    (cddr u))))
          ((and (pair? u) (equal? (car u) '^) (pair? (cdr u)) (pair? (cddr u))
                (un-rational-exp? (caddr u)))
           (let ((v (un-eval (cadr u))) (k (caddr u)))
             (cons (un-rpow (car v) k) (un-dim-scale (cdr v) k))))
          (else (error "units: не единица:" u))))

  (define (unit-factor u) (car (un-eval u)))
  (define (unit-dimension u) (cdr (un-eval u)))
  (define (same-dimension? u1 u2) (equal? (unit-dimension u1) (unit-dimension u2)))

  (define (dimension->string d)
    (let ((parts (filter (lambda (s) (not (equal? s "")))
                         (map2 (lambda (nm e)
                                 (cond ((= e 0) "")
                                       ((= e 1) nm)
                                       (else (string-append nm "^" (to-string e)))))
                               un-names d))))
      (if (null? parts)
          "1"
          (foldl (lambda (acc s) (string-append acc " " s)) (car parts) (cdr parts)))))

  ; ---------- величины ----------
  (define (quantity v u) (list 'quantity v u))
  (define (quantity? q) (and (pair? q) (equal? (car q) 'quantity) (= (length q) 3)))
  (define (quantity-value q) (cadr q))
  (define (quantity-unit q) (caddr q))

  (define (un-need-q q)
    (if (quantity? q) q (error "units: ожидается (quantity значение единица):" q)))

  (define (un-dim-error who d1 d2)
    (error (string-append who ": размерности различны: "
                          (dimension->string d1) " и " (dimension->string d2))))

  (define (convert q target)
    (un-need-q q)
    (let ((a (un-eval (quantity-unit q))) (b (un-eval target)))
      (if (equal? (cdr a) (cdr b))
          (quantity (* (quantity-value q) (/ (car a) (car b))) target)
          (un-dim-error "convert" (cdr a) (cdr b)))))

  (define (quantity-add a b)
    (un-need-q a)
    (un-need-q b)
    (let ((d1 (unit-dimension (quantity-unit a))) (d2 (unit-dimension (quantity-unit b))))
      (if (equal? d1 d2)
          (quantity (+ (quantity-value a) (quantity-value (convert b (quantity-unit a))))
                    (quantity-unit a))
          (un-dim-error "quantity-add" d1 d2))))

  (define (quantity-mul a b)
    (un-need-q a)
    (un-need-q b)
    (quantity (* (quantity-value a) (quantity-value b)) (list '* (quantity-unit a) (quantity-unit b))))

  (define (quantity-div a b)
    (un-need-q a)
    (un-need-q b)
    (quantity (/ (quantity-value a) (quantity-value b)) (list '/ (quantity-unit a) (quantity-unit b))))

  (define (quantity-pow q k)
    (un-need-q q)
    (if (un-rational-exp? k)
        (quantity (if (and (integer? k) (number? (quantity-value q)) (not (un-float? (quantity-value q))))
                      (un-ipow (quantity-value q) k)
                      (^ (quantity-value q) k))
                  (list '^ (quantity-unit q) k))
        (error "quantity-pow: показатель должен быть рациональным числом:" k)))

  ; ---------- температура (аффинный перевод через кельвины) ----------
  (define (un-temp-kelvin v u)
    (cond ((member? u '(K)) v)
          ((member? u '(°C degC)) (+ v 5463/20))
          ((member? u '(°F degF)) (/ (* 5 (+ v 45967/100)) 9))
          (else (error "convert-temperature: единица температуры K, °C, °F:" u))))

  (define (un-kelvin-temp k u)
    (cond ((member? u '(K)) k)
          ((member? u '(°C degC)) (- k 5463/20))
          ((member? u '(°F degF)) (- (/ (* 9 k) 5) 45967/100))
          (else (error "convert-temperature: единица температуры K, °C, °F:" u))))

  (define (convert-temperature v from to)
    (un-kelvin-temp (un-temp-kelvin v from) to))

  ; ---------- проверка размерности ----------
  (define (un-bad where d1 d2) (raise (list 'mismatch where d1 d2)))

  (define (un-env-dim s env)
    (let ((e (assoc s env)))
      (cond (e (let ((x (cdr e)))
                 (if (and (pair? x) (number? (car x))) x (unit-dimension x))))
            ((member? s '(pi %i %e)) un-zero)
            (else (error "dimension-check: не задана размерность символа" s)))))

  (define (un-same where dims)
    (let ((d0 (car dims)))
      (for-each (lambda (d) (if (equal? d d0) #f (un-bad where d0 d))) (cdr dims))
      d0))

  (define (un-chk f env)
    (cond ((number? f) un-zero)
          ((symbol? f) (un-env-dim f env))
          ((not (pair? f)) (error "dimension-check: не выражение:" f))
          (else
           (let ((h (car f)) (args (cdr f)))
             (cond
               ((member? h '(+ - min max = < > <= >=))
                (un-same f (map (lambda (a) (un-chk a env)) args)))
               ((equal? h '*)
                (foldl (lambda (acc a) (un-dim-add acc (un-chk a env))) un-zero args))
               ((equal? h '/)
                (let ((ds (map (lambda (a) (un-chk a env)) args)))
                  (if (null? (cdr ds))
                      (un-dim-scale (car ds) -1)
                      (foldl (lambda (acc d) (un-dim-add acc (un-dim-scale d -1))) (car ds) (cdr ds)))))
               ((equal? h 'abs) (un-chk (car args) env))
               ((equal? h 'sqrt) (un-chk (list '^ (car args) 1/2) env))
               ((equal? h '^)
                (let* ((d (un-chk (car args) env))
                       (k0 (cadr args))
                       (k (if (pair? k0) (simplify k0) k0)))
                  (cond ((equal? d un-zero) (un-same f (list un-zero (un-chk k0 env))))
                        ((un-rational-exp? k) (un-dim-scale d k))
                        (else (un-bad f d 'rational-exponent)))))
               ((member? h '(exp log ln sin cos tan asin acos atan sinh cosh tanh))
                (let ((d (un-chk (car args) env)))
                  (if (equal? d un-zero) un-zero (un-bad f d un-zero))))
               (else (error "dimension-check: неизвестная операция" h)))))))

  (define (dimension-check formula env)
    (try (list 'ok (un-chk formula env))
         (lambda (e)
           (let ((d (error-data e)))
             (if (and (pair? d) (equal? (car d) 'mismatch))
                 d
                 (raise e))))))

  ; ---------- π-теорема Бэкингема (DIM.2) ----------
  ; матрица — список строк (списков рациональных чисел)
  (define (un-pos x l)
    (let loop ((i 0) (r l))
      (cond ((null? r) #f) ((equal? (car r) x) i) (else (loop (+ i 1) (cdr r))))))

  (define (un-row-sub r p k) (map2 (lambda (a b) (- a (* k b))) r p))

  ; приведённая ступенчатая форма над ℚ: список (столбец-ведущего . строка), строки с единичным ведущим
  (define (un-rref m ncols)
    (let loop ((c 0) (rows m) (done '()))
      (if (= c ncols)
          (reverse done)
          (let ((p0 (let find ((r rows))
                      (cond ((null? r) #f) ((= (nth (car r) c) 0) (find (cdr r))) (else (car r))))))
            (if (not p0)
                (loop (+ c 1) rows done)
                (let* ((pv (nth p0 c))
                       (p (map (lambda (x) (/ x pv)) p0))
                       (others (map (lambda (r) (un-row-sub r p (nth r c)))
                                    (filter (lambda (r) (not (equal? r p0))) rows)))
                       (done2 (map (lambda (d) (cons (car d) (un-row-sub (cdr d) p (nth (cdr d) c)))) done)))
                  (loop (+ c 1) others (cons (cons c p) done2))))))))

  (define (un-rank m ncols) (length (un-rref m ncols)))

  ; базис ядра (A v = 0): по вектору на свободный столбец
  (define (un-nullspace m ncols)
    (let* ((rr (un-rref m ncols)) (pivs (map car rr)))
      (map (lambda (f)
             (map (lambda (c)
                    (cond ((= c f) 1)
                          ((member? c pivs) (- (nth (cdr (assoc c rr)) f)))
                          (else 0)))
                  (range ncols)))
           (filter (lambda (c) (not (member? c pivs))) (range ncols)))))

  ; целые взаимно простые показатели, первый ненулевой положителен
  (define (un-int-normalize v)
    (let* ((l (foldl (lambda (acc x) (lcm acc (denom x))) 1 v))
           (w (map (lambda (x) (* x l)) v))
           (g (foldl (lambda (acc x) (gcd acc x)) 0 w))
           (w2 (map (lambda (x) (/ x g)) w))
           (s (let f ((r w2)) (cond ((null? r) 1) ((= (car r) 0) (f (cdr r))) ((< (car r) 0) -1) (else 1)))))
      (map (lambda (x) (* x s)) w2)))

  (define (un-group-expr vars exps)
    (cons '* (filter (lambda (x) x)
                     (map2 (lambda (v e) (if (= e 0) #f (list '^ v e))) vars exps))))

  ; группа → список (переменная . показатель) или #f, если форма не (* (^ v a) …)
  (define (un-parse-group g)
    (let ((fs (cond ((and (pair? g) (equal? (car g) '*)) (cdr g)) (else (list g)))))
      (let ((ps (map (lambda (f)
                       (cond ((symbol? f) (cons f 1))
                             ((and (pair? f) (equal? (car f) '^) (= (length f) 3)
                                   (symbol? (cadr f)) (un-rational-exp? (caddr f)))
                              (cons (cadr f) (caddr f)))
                             (else #f)))
                     fs)))
        (if (every? (lambda (p) p) ps) ps #f))))

  (define (un-vars-check vars)
    (for-each (lambda (v) (if (symbol? v) #f (error "units: переменная должна быть символом:" v))) vars)
    (if (= (length vars) (length (un-dedup vars))) #f (error "units: повторяющиеся переменные:" vars)))

  (define (un-dedup l)
    (foldl (lambda (acc x) (if (member? x acc) acc (append acc (list x)))) '() l))

  (define (un-dims vars env) (map (lambda (v) (un-env-dim v env)) vars))

  (define (un-matrix dims)
    (filter (lambda (row) (not (every? (lambda (x) (= x 0)) row)))
            (map (lambda (i) (map (lambda (d) (nth d i)) dims)) (range 7))))

  ; матрица размерностей: строки — базовые величины (нулевые строки опущены), столбцы — vars
  (define (dimension-matrix vars env)
    (un-vars-check vars)
    (un-matrix (un-dims vars env)))

  (define (un-cols m idxs) (map (lambda (row) (map (lambda (i) (nth row i)) idxs)) m))

  (define (un-groups-repeating vars m rep)
    (let* ((n (length vars)) (r (un-rank m n))
           (ridx (map (lambda (v)
                        (or (un-pos v vars)
                            (error "pi-groups: повторяющаяся переменная не из списка:" v)))
                      rep)))
      (if (not (= (length rep) (length (un-dedup rep))))
          (error "pi-groups: повторы в :repeating" rep))
      (if (not (and (= (length rep) r) (= (un-rank (un-cols m ridx) (length rep)) r)))
          (error "pi-groups: недопустимый набор :repeating (нужно ровно rank = "
                 r " переменных с независимыми столбцами размерностей):" rep))
      (map (lambda (j)
             (let* ((j-i (un-pos j vars))
                    (idx (append ridx (list j-i)))
                    (v (car (un-nullspace (un-cols m idx) (length idx))))
                    (vj (nth v r))
                    (exps (map (lambda (i)
                                 (let ((p (un-pos i idx))) (if p (/ (nth v p) vj) 0)))
                               (range n))))
               (un-group-expr vars exps)))
           (filter (lambda (v) (not (member? v rep))) vars))))

  ; независимые безразмерные произведения; :repeating (v …) — классический метод
  (define (pi-groups vars env &rest opts)
    (un-vars-check vars)
    (let ((m (un-matrix (un-dims vars env))) (n (length vars)))
      (cond ((null? opts)
             (map (lambda (v) (un-group-expr vars (un-int-normalize v))) (un-nullspace m n)))
            ((and (equal? (car opts) :repeating) (pair? (cdr opts)) (null? (cddr opts)))
             (un-groups-repeating vars m (cadr opts)))
            (else (error "pi-groups: ожидается :repeating список" opts)))))

  ; сертификат: группы безразмерны, независимы, их число = n − rank
  (define (pi-groups-check vars env groups)
    (try
     (let* ((n (length vars))
            (parsed (map un-parse-group groups))
            (m (un-matrix (un-dims vars env))))
       (and (every? (lambda (p) p) parsed)
            (every? (lambda (p)
                      (and (every? (lambda (e) (member? (car e) vars)) p)
                           (= (length p) (length (un-dedup (map car p))))))
                    parsed)
            (every? (lambda (g) (equal? (dimension-check g env) (list 'ok un-zero))) groups)
            (let ((em (map (lambda (p)
                             (map (lambda (v) (let ((e (assoc v p))) (if e (cdr e) 0))) vars))
                           parsed)))
              (and (= (un-rank em n) (length groups))
                   (= (length groups) (- n (un-rank m n)))))))
     (lambda (e) #f)))

  ; target = C · ∏ vᵢ^aᵢ, если групп ровно одна; иначе (= (Phi π₁ … πₖ) 0)
  (define (dimensional-solve target vars env)
    (if (member? target vars) (error "dimensional-solve: target входит в vars" target))
    (let* ((all (append vars (list target))) (gs (pi-groups all env)))
      (cond
        ((null? gs) (error "dimensional-solve: безразмерных групп нет — размерностей недостаточно"))
        ((null? (cdr gs))
         (let* ((al (un-parse-group (car gs))) (t (assoc target al)))
           (if (not t)
               (error "dimensional-solve: target не входит в безразмерную группу" (car gs)))
           (let* ((fs (filter (lambda (x) x)
                              (map (lambda (v)
                                     (let ((e (assoc v al)))
                                       (if e (list '^ v (/ (- (cdr e)) (cdr t))) #f)))
                                   vars)))
                  (rel (list '= target (cons '* (cons 'C fs)))))
             (if (equal? (car (dimension-check rel (append env (list (cons 'C un-zero))))) 'ok)
                 rel
                 (error "dimensional-solve: сертификат размерности не прошёл" rel)))))
        (else (list '= (cons 'Phi gs) 0)))))
