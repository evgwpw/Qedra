; intbasis.lisp — A4.2: целый базис общей кривой F(x,y) = 0 (ван Хуй через Пюизё).
;
; Кривая: F ∈ ℚ[x][y], унитарен по y, n = deg_y F.  Целый базис — базис модуля
; элементов ℚ(x,y), целых во всех ветвях над всеми конечными точками.
;
; Локально в точке a (сдвиг x := x − a, a — корень disc_y F) ищем элементы
;     w = Σ_{k=0..D} Σ_{i<n} c[k,i]·x^{k−D}·y^i,   c[k,i] ∈ ℚ,
; целые в каждой ветви Пюизё: v_j(w) ≥ 0.  В ветви x = t^q, y = Σ c_e t^{e·q}
; это значит: все коэффициенты при t^m, m < 0, равны нулю.
;
; Глубина D = v_a(disc_y F): кондуктор порядка 2δ не больше v_a(disc), поэтому
; знаменателей x^{−D} хватает; это проверяет сертификат (b) — если индекс в
; точке не обнулился, ответ unknown.
;
; Коэффициенты рядов — константы в ℚ(√d, ζ); арифметика точная: элемент —
; список ((d₁ … d_k) . c), где d_i — бесквадратные целые, c ∈ ℚ, а произведение
; √d_i считается по правилу √d·√d = d.  Кубические радикалы и root-of дают
; честный unknown (в тестовых кривых их нет).
;
; Глобально: стандартный базис {1, y, …, y^{n−1}} + локальные поправки всех
; точек → треугольная нормализация над ℚ[x] (HNF) → базис.

(module integrate
  (export integral-basis integral-basis-check-general))

; ---------- рациональные числа и бесквадратные части ----------

(define (ib-rat? x)
  (and (number? x) (or (integer? x) (equal? (type-of x) 'rational))))

(define (ib-factor-int n)
  (let loop ((m n) (p 2) (acc '()))
    (cond ((= m 1) (reverse acc))
          ((> (* p p) m) (reverse (cons (cons m 1) acc)))
          ((= 0 (remainder m p))
           (let div ((m2 m) (e 0))
             (if (= 0 (remainder m2 p))
                 (div (quotient m2 p) (+ e 1))
                 (loop m2 (+ p 1) (cons (cons p e) acc)))))
          (else (loop m (+ p 1) acc)))))

; n ≠ 0 → (sf . s): n = sf·s², sf бесквадратное (знак сохранён)
(define (ib-sf-int n)
  (let* ((sg (if (< n 0) -1 1))
         (fs (ib-factor-int (abs n))))
    (let loop ((fs fs) (sf sg) (s 1))
      (if (null? fs)
          (cons sf s)
          (let* ((p (car (car fs))) (e (cdr (car fs))))
            (loop (cdr fs)
                  (if (= 1 (remainder e 2)) (* sf p) sf)
                  (* s (ib-ipow p (quotient e 2)))))))))

(define (ib-ipow p k)
  (if (= k 0) 1 (* p (ib-ipow p (- k 1)))))

; √q для рационального q (q ≠ 0) → элемент поля коэффициентов
(define (ib-k-sqrt-rat q)
  (if (= q 0)
      '()
      (let* ((neg (< q 0))
             (a (abs q))
             (nu (numer (together a)))
             (de (denom (together a)))
             (fn (ib-sf-int nu))
             (fd (ib-sf-int de))
             (sf (* (if neg -1 1) (car fn) (car fd)))
             (s (/ (cdr fn) (* (cdr fd) (car fd)))))
        (list (cons (if (= sf 1) '() (list sf)) s)))))

; ---------- элементы ℚ(√d): канонический вид ----------

(define (ib-assoc k al)
  (cond ((null? al) #f) ((equal? (car (car al)) k) (car al)) (else (ib-assoc k (cdr al)))))

(define (ib-k-zero? e) (null? e))
(define (ib-k-one) (list (cons '() 1)))

; добавить член c·√(∏d) к элементу
(define (ib-k-add-term e f c)
  (if (= c 0)
      e
      (let ((p (ib-assoc f e)))
        (if p
            (let ((s (+ (cdr p) c)))
              (if (= s 0)
                  (filter (lambda (t) (not (equal? (car t) f))) e)
                  (map (lambda (t) (if (equal? (car t) f) (cons f s) t)) e)))
            (cons (cons f c) e)))))

(define (ib-k-add a b)
  (foldl (lambda (acc t) (ib-k-add-term acc (car t) (cdr t))) a b))

(define (ib-k-scale a c)
  (if (= c 0)
      '()
      (foldl (lambda (acc t) (ib-k-add-term acc (car t) (* (cdr t) c))) '() a)))

; произведение списков бесквадратных: √d·√d = d
(define (ib-fmul f g)
  (let loop ((a (sort (append f g) <)) (res '()) (c 1))
    (if (null? a)
        (cons (reverse res) c)
        (if (and (pair? (cdr a)) (= (car a) (cadr a)))
            (loop (cddr a) res (* c (car a)))
            (loop (cdr a) (cons (car a) res) c)))))

(define (ib-k-mul a b)
  (foldl (lambda (acc ta)
           (foldl (lambda (acc2 tb)
                    (let* ((m (ib-fmul (car ta) (car tb)))
                           (f (car m))
                           (c (* (cdr ta) (cdr tb) (cdr m))))
                      (ib-k-add-term acc2 f c)))
                  acc b))
         '() a))

(define (ib-k-fprod f) (foldl (lambda (acc d) (* acc d)) 1 f))

; обратный: 1/(c·∏√d) = (∏√d)/(c·∏d)
(define (ib-k-inv a)
  (if (and (pair? a) (null? (cdr a)))
      (let* ((t (car a)) (f (car t)) (c (cdr t)))
        (list (cons f (/ 1 (* c (ib-k-fprod f))))))
      #f))

(define (ib-k-pow-el k p)
  (let loop ((p p) (base k) (acc (ib-k-one)))
    (if (= p 0)
        acc
        (loop (quotient p 2)
              (ib-k-mul base base)
              (if (= 1 (remainder p 2)) (ib-k-mul acc base) acc)))))

; разбор выражения-константы; #f — не поддерживается (x/y, кубический радикал)
(define (ib-k-parse e)
  (let ((e (simplify e)))
    (cond
      ((ib-rat? e) (if (= e 0) '() (list (cons '() e))))
      ((equal? e '%i) (list (cons (list -1) 1)))
      ((pair? e)
       (let ((op (car e)) (as (cdr e)))
         (cond
           ((equal? op '+) (ib-k-sum as))
           ((equal? op '*) (ib-k-prod as))
           ((equal? op '-) (ib-k-diff as))
           ((equal? op '/) (ib-k-quot as))
           ((equal? op '^) (ib-k-pow (car as) (cadr as)))
           (else #f))))
      (else #f))))

(define (ib-k-sum as)
  (let loop ((as as) (acc '()))
    (if (null? as)
        acc
        (let ((k (ib-k-parse (car as))))
          (if (equal? k #f) #f (loop (cdr as) (ib-k-add acc k)))))))

(define (ib-k-prod as)
  (let loop ((as as) (acc (ib-k-one)))
    (if (null? as)
        acc
        (let ((k (ib-k-parse (car as))))
          (if (equal? k #f) #f (loop (cdr as) (ib-k-mul acc k)))))))

(define (ib-k-diff as)
  (if (null? (cdr as))
      (let ((k (ib-k-parse (car as))))
        (if (equal? k #f) #f (ib-k-scale k -1)))
      (let ((k (ib-k-parse (car as))))
        (if (equal? k #f)
            #f
            (let loop ((rest (cdr as)) (acc k))
              (if (null? rest)
                  acc
                  (let ((b (ib-k-parse (car rest))))
                    (if (equal? b #f)
                        #f
                        (loop (cdr rest) (ib-k-add acc (ib-k-scale b -1)))))))))))

(define (ib-k-quot as)
  (let ((a (ib-k-parse (car as))))
    (if (equal? a #f)
        #f
        (let loop ((rest (cdr as)) (acc a))
          (if (null? rest)
              acc
              (let ((b (ib-k-parse (car rest))))
                (if (equal? b #f)
                    #f
                    (let ((ib (ib-k-inv b)))
                      (if (equal? ib #f)
                          #f
                          (loop (cdr rest) (ib-k-mul acc ib)))))))))))

(define (ib-k-pow b p)
  (let ((b (simplify b)) (p (simplify p)))
    (cond
      ((and (ib-rat? b) (equal? p 1/2)) (ib-k-sqrt-rat b))
      ((and (ib-rat? b) (equal? p -1/2)) (ib-k-inv (ib-k-sqrt-rat b)))
      ((and (ib-rat? b) (equal? p 3/2))
       (ib-k-mul (list (cons '() b)) (ib-k-sqrt-rat b)))
      ((integer? p)
       (let ((k (ib-k-parse b)))
         (cond ((equal? k #f) #f)
               ((>= p 0) (ib-k-pow-el k p))
               (else (let ((iv (ib-k-inv k)))
                       (if (equal? iv #f) #f (ib-k-pow-el iv (- p))))))))
      (else #f))))

(define (ib-k-coeff e f)
  (let ((p (ib-assoc f e))) (if p (cdr p) 0)))

; ---------- независимость классов √d над ℚ ----------

(define (ib-prime-vec d)
  (let ((sg (if (< d 0) (list -1) '()))
        (fs (ib-factor-int (abs d))))
    (sort (append sg (map car fs)) <)))

(define (ib-xor a b)
  (cond ((null? a) b)
        ((null? b) a)
        ((< (car a) (car b)) (cons (car a) (ib-xor (cdr a) b)))
        ((> (car a) (car b)) (cons (car b) (ib-xor a (cdr b))))
        (else (ib-xor (cdr a) (cdr b)))))

(define (ib-member? x l)
  (cond ((null? l) #f) ((equal? x (car l)) #t) (else (ib-member? x (cdr l)))))

(define (ib-f2-reduce v basis)
  (let loop ((v v))
    (if (null? v)
        '()
        (let ((b (ib-find-head basis (car v))))
          (if b (loop (ib-xor v b)) v)))))

(define (ib-find-head basis p)
  (cond ((null? basis) #f)
        ((ib-member? p (car basis)) (car basis))
        (else (ib-find-head (cdr basis) p))))

(define (ib-f2-independent? ds)
  (let loop ((ds ds) (basis '()))
    (if (null? ds)
        #t
        (let ((r (ib-f2-reduce (ib-prime-vec (car ds)) basis)))
          (if (null? r) #f (loop (cdr ds) (cons r basis)))))))

; ---------- ряды Пюизё с коэффициентами в ℚ(√d) ----------

; ветвь (q ((c e) …)) → (q . ((порядок . элемент) …)) | #f
(define (ib-ser-branch br)
  (let ((q (car br)))
    (let loop ((ts (cadr br)) (acc '()))
      (if (null? ts)
          (cons q (reverse acc))
          (let* ((te (car ts))
                 (c (ib-k-parse (car te)))
                 (o (* (cadr te) q)))
            (if (or (equal? c #f) (not (integer? o)))
                #f
                (loop (cdr ts) (cons (cons o c) acc))))))))

(define (ib-ser-add-term s o k)
  (if (or (not k) (null? k))
      s
      (let ((p (ib-assoc o s)))
        (if p
            (let ((sum (ib-k-add (cdr p) k)))
              (if (null? sum)
                  (filter (lambda (t) (not (= (car t) o))) s)
                  (map (lambda (t) (if (= (car t) o) (cons o sum) t)) s)))
            (cons (cons o k) s)))))

(define (ib-ser-mul a b limit)
  (foldl (lambda (acc ta)
           (foldl (lambda (acc2 tb)
                    (let ((o (+ (car ta) (car tb))))
                      (if (> o limit)
                          acc2
                          (ib-ser-add-term acc2 o (ib-k-mul (cdr ta) (cdr tb))))))
                  acc b))
         '() a))

(define (ib-ser-pow s i limit)
  (let loop ((k 0) (acc (list (cons 0 (ib-k-one)))))
    (if (= k i) acc (loop (+ k 1) (ib-ser-mul acc s limit)))))

; ---------- локальная система ----------

(define (ib-range-from lo hi)
  (if (> lo hi) '() (cons lo (ib-range-from (+ lo 1) hi))))

; строки условий по всем ветвям: строка — список элементов поля для неизвестных (k,i)
(define (ib-local-rows sers n D)
  (let* ((qmax (foldl (lambda (m s) (if (> (car s) m) (car s) m)) 0 sers))
         (limit (* D qmax))
         (pows (map (lambda (s)
                      (list (car s)
                            (map (lambda (i) (ib-ser-pow (cdr s) i limit)) (range n))))
                    sers)))
    (foldl
     (lambda (rows sq)
       (let* ((q (car sq))
              (ps (cadr sq))
              (lo (- (* D q))))
         (foldl
          (lambda (rows o)
            (cons
             (map (lambda (j)
                    (let* ((k (quotient j n))
                           (i (remainder j n))
                           (sh (* (- k D) q))
                           (p (ib-assoc (- o sh) (nth ps i))))
                      (if p (cdr p) '())))
                  (range (* n (+ D 1))))
             rows))
          rows (ib-range-from lo -1))))
     '() pows)))

(define (ib-fl-cmp a b)
  (cond ((and (null? a) (null? b)) 0)
        ((null? a) -1)
        ((null? b) 1)
        ((< (car a) (car b)) -1)
        ((> (car a) (car b)) 1)
        (else (ib-fl-cmp (cdr a) (cdr b)))))

(define (ib-unique l)
  (let loop ((l l) (acc '()))
    (if (null? l)
        (reverse acc)
        (if (ib-member? (car l) acc) (loop (cdr l) acc) (loop (cdr l) (cons (car l) acc))))))

; все бесквадратные d, встречающиеся в строках
(define (ib-row-radicands rows)
  (ib-unique (foldl (lambda (acc row)
                      (foldl (lambda (acc k)
                               (foldl (lambda (acc t) (append (car t) acc)) acc k))
                             acc row))
                    '() rows)))

; все наборы-ключи (для базиса поля коэффициентов)
(define (ib-row-keys rows)
  (sort (ib-unique (foldl (lambda (acc row)
                            (foldl (lambda (acc k)
                                     (foldl (lambda (acc t) (cons (car t) acc)) acc k))
                                   acc row))
                          '() rows))
        (lambda (a b) (< (ib-fl-cmp a b) 0))))

; строки K → строки ℚ по базису ключей
(define (ib-expand-rows rows keys)
  (foldl (lambda (acc row)
           (append (map (lambda (key) (map (lambda (k) (ib-k-coeff k key)) row)) keys) acc))
         '() rows))

; вектор ядра → примитивный целочисленный (общий знаменатель и НОД числителей):
; без этого HNF над ℚ[x] захлёбывается в коэффициентах
(define (ib-lcm a b)
  (if (or (= a 0) (= b 0)) 0 (/ (abs (* a b)) (gcd a b))))

(define (ib-primitive v)
  (let* ((L (foldl (lambda (acc c) (ib-lcm acc (denom (together c)))) 1 v))
         (ints (map (lambda (c) (* c L)) v))
         (g (foldl (lambda (acc c) (gcd acc (abs c))) 0 ints)))
    (if (= g 0) v (map (lambda (c) (/ c g)) ints))))

; вектор ядра → элемент: список n пар (числитель . знаменатель), знаменатель x^D
(define (ib-kernel->elements K n D x)
  (map
   (lambda (v)
     (map (lambda (i)
            (let loop ((j i) (num '()))
              (if (>= j (length v))
                  (cons (ib-poly->expr num x) (list '^ x D))
                  (let* ((c (nth v j))
                         (k (quotient j n))
                         (e (- k D)))
                    (loop (+ j n) (if (= c 0) num (ib-p-add num (ib-p-mono (+ e D) c))))))))
          (range n)))
   K))

; ---------- многочлены от x над ℚ (списки коэффициентов по возрастанию) ----------

(define (ib-p-trim p)
  (cond ((null? p) '())
        ((= (car (reverse p)) 0) (ib-p-trim (reverse (cdr (reverse p)))))
        (else p)))

(define (ib-p-zero? p) (null? (ib-p-trim p)))
(define (ib-p-deg p) (- (length (ib-p-trim p)) 1))
(define (ib-p-lc p) (car (reverse (ib-p-trim p))))

(define (ib-p-mono k c)
  (if (= c 0) '() (append (map (lambda (i) 0) (range k)) (list c))))

(define (ib-p-add a b)
  (let loop ((a a) (b b) (acc '()))
    (cond ((null? a) (append (reverse acc) b))
          ((null? b) (append (reverse acc) a))
          (else (loop (cdr a) (cdr b) (cons (+ (car a) (car b)) acc))))))

(define (ib-p-neg a) (map (lambda (c) (- c)) a))

(define (ib-p-sub a b) (ib-p-add a (ib-p-neg b)))

(define (ib-p-scale a c) (map (lambda (x) (* x c)) a))

(define (ib-p-mul a b)
  (if (or (null? a) (null? b))
      '()
      (let* ((na (length a)) (nb (length b))
             (r (map (lambda (i) 0) (range (+ na nb -1)))))
        (let loop ((i 0) (r r))
          (if (>= i na)
              (ib-p-trim r)
              (let ((ai (nth a i)))
                (loop (+ i 1)
                      (if (= ai 0)
                          r
                          (map (lambda (j)
                                 (if (or (< j i) (>= j (+ i nb)))
                                     (nth r j)
                                     (+ (nth r j) (* ai (nth b (- j i))))))
                               (range (length r)))))))))))

(define (ib-p-divmod a b)
  (let ((db (ib-p-deg b)) (lb (ib-p-lc b)))
    (let loop ((r a) (q '()))
      (if (or (ib-p-zero? r) (< (ib-p-deg r) db))
          (list (ib-p-trim q) (ib-p-trim r))
          (let* ((dr (ib-p-deg r))
                 (c (/ (ib-p-lc r) lb))
                 (k (- dr db))
                 (m (ib-p-mono k c)))
            (loop (ib-p-sub r (ib-p-mul m b))
                  (ib-p-add q m)))))))

(define (ib-p-monic p) (ib-p-scale p (/ 1 (ib-p-lc p))))

; расширенный Евклид: (g s t), g = s·a + t·b, g монический
(define (ib-p-egcd a b)
  (if (ib-p-zero? b)
      (if (ib-p-zero? a)
          (list '() '() '())
          (list (ib-p-monic a) (list (/ 1 (ib-p-lc a))) '()))
      (let* ((qr (ib-p-divmod a b))
             (q (car qr)) (r (cadr qr))
             (gst (ib-p-egcd b r))
             (g (car gst)) (s (cadr gst)) (t (caddr gst)))
        (list g t (ib-p-sub s (ib-p-mul q t))))))

; ---------- векторы коэффициентов и HNF над ℚ[x] ----------

(define (ib-vec-zero? v)
  (foldl (lambda (acc p) (and acc (ib-p-zero? p))) #t v))

(define (ib-vec-pivot v)
  (let loop ((i (- (length v) 1)))
    (if (< i 0) -1 (if (ib-p-zero? (nth v i)) (loop (- i 1)) i))))

(define (ib-vec-add a b) (map2 ib-p-add a b))
(define (ib-vec-sub a b) (map2 ib-p-sub a b))
(define (ib-vec-scale v c) (map (lambda (p) (ib-p-mul p c)) v))

(define (ib-vec-monic v)
  (let ((i (ib-vec-pivot v)))
    (if (< i 0)
        v
        (let ((lc (ib-p-lc (nth v i))))
          (if (= lc 1) v (map (lambda (p) (ib-p-scale p (/ 1 lc))) v))))))

; HNF строк над ℚ[x]: на каждый индекс y — один ряд с моническим ведущим
(define (ib-hnf rows n)
  (let loop ((rows (filter (lambda (v) (not (ib-vec-zero? v))) rows)) (done '()))
    (if (null? rows)
        (reverse done)
        (let* ((i (foldl (lambda (m v) (if (> (ib-vec-pivot v) m) (ib-vec-pivot v) m)) -1 rows))
               (at-i (filter (lambda (v) (= (ib-vec-pivot v) i)) rows))
               (rest (filter (lambda (v) (< (ib-vec-pivot v) i)) rows)))
          (let comb ((rs (cdr at-i)) (r (ib-vec-monic (car at-i))) (rest rest))
            (if (null? rs)
                (loop rest (cons r done))
                (let* ((s (car rs))
                       (gst (ib-p-egcd (nth r i) (nth s i)))
                       (g (car gst)) (a (cadr gst)) (b (caddr gst))
                       (r2 (ib-vec-monic (ib-vec-add (ib-vec-scale r a) (ib-vec-scale s b))))
                       (q (car (ib-p-divmod (nth s i) g)))
                       (s2 (ib-vec-sub s (ib-vec-scale r2 q))))
                  (comb (cdr rs) r2
                        (if (ib-vec-zero? s2) rest (cons s2 rest))))))))))

; ---------- выражения ----------

(define (ib-poly->expr p x)
  (let ((p (ib-p-trim p)))
    (if (null? p)
        0
        (let loop ((k 0) (ps p) (acc '()))
          (if (null? ps)
              (if (null? acc) 0 (simplify (cons '+ (reverse acc))))
              (loop (+ k 1) (cdr ps)
                    (if (= (car ps) 0)
                        acc
                        (cons (if (= k 0)
                                  (car ps)
                                  (list '* (car ps) (list '^ x k)))
                              acc))))))))

(define (ib-polys->expr ps T x)
  (if (null? ps)
      0
      (simplify (cons '+ (map (lambda (i)
                                (let ((p (nth ps i)))
                                  (if (ib-p-zero? p)
                                      0
                                      (list '* (ib-poly->expr p x) (list '^ T i)))))
                              (range (length ps)))))))

(define (ib-vec->expr v y x D)
  (simplify (cons '+ (map (lambda (i)
                            (let ((p (nth v i)))
                              (if (ib-p-zero? p)
                                  0
                                  (list '* (list '/ (ib-poly->expr p x) D)
                                        (list '^ y i)))))
                          (range (length v))))))

; разбор многочлена от x с рациональными коэффициентами
(define (ib-poly-parse e x)
  (let ((e (expand (simplify e))))
    (if (equal? e 0)
        '()
        (let ((d (try (degree e x) (lambda (err) 0))))
          (if (not (and (integer? d) (>= d 0)))
              #f
              (let loop ((k 0) (acc '()))
                (if (> k d)
                    (ib-p-trim (reverse acc))
                    (let ((c (try (coeff e x k) (lambda (err) 0))))
                      (if (ib-rat? c)
                          (loop (+ k 1) (cons c acc))
                          #f)))))))))

(define (ib-remove-one e l)
  (cond ((null? l) '())
        ((equal? e (car l)) (cdr l))
        (else (cons (car l) (ib-remove-one e (cdr l))))))

(define (ib-prod-expr l)
  (cond ((null? l) 1)
        ((null? (cdr l)) (if (equal? (car l) 1) 1 (car l)))
        (else (list '* (car l) (ib-prod-expr (cdr l))))))

; общий знаменатель: векторы (num . den) → (rows . D) с полиномиальными строками
(define (ib-vecs-clear-denoms vecs n x)
  (let* ((dens (ib-unique (foldl (lambda (acc v)
                                   (foldl (lambda (acc e) (cons (cdr e) acc)) acc v))
                                 '() vecs)))
         (D (ib-prod-expr dens))
         (rows
          (map (lambda (v)
                 (map (lambda (e)
                        (let ((num (ib-poly-parse (car e) x))
                              (rest (ib-poly-parse (ib-prod-expr (ib-remove-one (cdr e) dens)) x)))
                          (if (and (not (equal? num #f)) (not (equal? rest #f)))
                              (ib-p-mul num rest)
                              #f)))
                      v))
               vecs)))
    (if (foldl (lambda (ok r) (and ok (not (ib-member? #f r)))) #t rows)
        (cons rows D)
        'unknown)))

; ---------- точки дискриминанта ----------

(define (ib-linear-root g x)
  (let ((g (expand g)))
    (if (not (= (try (degree g x) (lambda (e) 0)) 1))
        'unknown
        (let ((c (coeff g x 1)) (d (coeff g x 0)))
          (if (ib-rat? c) (simplify (/ (- d) c)) 'unknown)))))

(define (ib-disc-points disc x)
  (let ((fs (try (factor-list (expand disc)) (lambda (e) #f))))
    (if (not fs)
        'unknown
        (let loop ((fs (cdr fs)) (acc '()))
          (if (null? fs)
              (reverse acc)
              (let* ((f (car fs)) (g (car f)) (e (cadr f)))
                (if (< e 2)
                    (loop (cdr fs) acc)
                    (let ((a (ib-linear-root g x)))
                      (if (equal? a 'unknown)
                          'unknown
                          (if (> e 30) 'unknown (loop (cdr fs) (cons (cons a e) acc))))))))))))

; ---------- локальный шаг ----------

(define (ib-shift-entry ent a x)
  (if (= a 0)
      ent
      (cons (expand (subst (list (list x (list '- x a))) (car ent)))
            (expand (subst (list (list x (list '- x a))) (cdr ent))))))

(define (ib-sers-ok? sers)
  (foldl (lambda (ok s)
           (and ok
                (foldl (lambda (ok2 t) (and ok2 (>= (car t) 0))) #t (cdr s))))
         #t sers))

(define (ib-local-elements F n a D x y)
  (if (> D 30)
      'unknown
      (let* ((Fa (if (= a 0) F (expand (subst (list (list x (list '+ x a))) F))))
             ; запас по длине ряда: цикл по D (ib-basis-monic) не должен пересчитывать Пюизё на каждом шаге
             (brs (try (px-cached Fa x y (max 8 (+ D 2))) (lambda (e) #f))))
        (if (or (not brs) (null? brs))
            'unknown
            (let ((sers (map ib-ser-branch brs)))
              (if (not (foldl (lambda (ok s) (and ok (not (equal? s #f)))) #t sers))
                  'unknown
                  (if (not (ib-sers-ok? sers))
                      'unknown
                      (let* ((rows (ib-local-rows sers n D))
                             (rads (ib-row-radicands rows))
                             (keys (ib-row-keys rows)))
                        (if (not (ib-f2-independent? rads))
                            'unknown
                            (let ((M (ib-expand-rows rows keys)))
                              (if (null? M)
                                  'unknown
                                  (let ((K (try (nullspace M) (lambda (e) #f))))
                                    (if (equal? K #f)
                                        'unknown
                                        (map (lambda (el)
                                               (map (lambda (ent) (ib-shift-entry ent a x)) el))
                                             (ib-kernel->elements (map ib-primitive K) n D x)))))))))))))))

; ---------- сборка ----------

(define (ib-ydeg F y)
  (let ((d (try (degree (expand F) y) (lambda (e) #f))))
    (if (and d (> d 0)) d #f)))

(define (ib-unital? F y)
  (let ((n (ib-ydeg F y)))
    (and n (equal? (simplify (coeff (expand F) y n)) 1))))

(define (ib-take l k) (if (= k 0) '() (cons (car l) (ib-take (cdr l) (- k 1)))))
(define (ib-drop l k) (if (= k 0) l (ib-drop (cdr l) (- k 1))))

(define (ib-minor m j)
  (map (lambda (row) (append (ib-take row j) (ib-drop row (+ j 1)))) (cdr m)))

; определитель матрицы многочленов (разложение по первой строке)
(define (ib-det m)
  (cond ((null? m) (list 1))
        ((null? (cdr m)) (car (car m)))
        (else
         (let loop ((j 0) (row (car m)) (acc '()) (sgn 1))
           (if (null? row)
               (if (= sgn 1) acc (ib-p-neg acc))
               (let ((term (ib-p-scale (ib-p-mul (car row) (ib-det (ib-minor m j))) sgn)))
                 (loop (+ j 1) (cdr row) (ib-p-add acc term) (- sgn))))))))

; элемент → вектор коэффициентов по y (числители . общий знаменатель)
(define (ib-basis->vecs basis n x y)
  (let ((vs (map (lambda (w)
                   (let ((u (try (together w) (lambda (e) #f))))
                     (if (equal? u #f)
                         #f
                         (let ((num (expand (numer u))) (den (expand (denom u))))
                           (if (contains-sym? den y)
                               #f
                               (map (lambda (i) (cons (expand (coeff num y i)) den))
                                    (range n)))))))
                 basis)))
    (if (foldl (lambda (ok v) (and ok (not (equal? v #f)))) #t vs) vs #f)))

; вектор индексов δ'_a = n·v_a(D) − v_a(det P) по уже найденным точкам дискриминанта
(define (ib-index-vec pts detP D n x)
  (let ((Dp (ib-poly-parse D x)))
    (if (equal? Dp #f)
        'unknown
        (map (lambda (p)
               (let ((a (car p)))
                 (- (* n (ib-val-at Dp a x)) (ib-val-at detP a x))))
             pts))))

; один проход при фиксированной глубине D: (базис флаг-отказа detP D) | unknown
(define (ib-basis-once F n x y D)
  (let* ((disc (expand (resultant F (diff y F) y)))
         (pts (ib-disc-points disc x)))
    (if (equal? pts 'unknown)
        'unknown
        (let ((res (foldl
                    (lambda (acc p)
                      (let ((els (ib-local-elements F n (car p) (min D (cdr p)) x y)))
                        (if (equal? els 'unknown)
                            (list (car acc) #t)                 ; точку пропускаем, флаг отказа
                            (list (append els (car acc)) (cadr acc)))))
                    (list '() #f) pts)))
          (let* ((locals (car res)) (failed (cadr res))
                 (std (map (lambda (i)
                            (map (lambda (j) (if (= i j) (cons 1 1) (cons 0 1)))
                                 (range n)))
                          (range n)))
                 (cleared (ib-vecs-clear-denoms (append std locals) n x)))
            (if (equal? cleared 'unknown)
                'unknown
                (let* ((rows (ib-hnf (car cleared) n))
                       (Dv (cdr cleared)))
                  (if (or (not rows) (not (= (length rows) n)))
                      'unknown
                      (list (map (lambda (v) (ib-vec->expr v y x Dv)) rows)
                            failed (ib-det rows) Dv)))))))))

; базис: глубина D растёт, пока индекс δ'_a не совпадёт с δ особых точек (по точкам);
; если singular-points не даёт чисел, останавливаемся на неподвижной точке индекса
(define (ib-basis-monic F n x y)
  (let* ((discExpr (expand (resultant F (diff y F) y)))
         (discF (ib-poly-parse discExpr x))
         (pts (if discF (ib-disc-points discExpr x) 'unknown)))
    (if (or (equal? discF #f) (equal? pts 'unknown))
        'unknown
        (let ((expect (map (lambda (p) (ib-sing-sum (car p) F x y)) pts)))
          (let ((known (not (ib-member? 'unknown expect))))
            (let loop ((D 1) (prev #f))
              (let ((res (ib-basis-once F n x y D)))
                (if (equal? res 'unknown)
                    'unknown
                    (let* ((basis (car res)) (failed (cadr res))
                           (detP (nth res 2)) (Dv (nth res 3))
                           (idx (ib-index-vec pts detP Dv n x)))
                      (cond
                        ((and known (equal? idx expect)) basis)
                        (failed 'unknown)
                        ((and (not known) prev (equal? idx prev)) basis)
                        ((>= D 12) 'unknown)
                        (else (loop (+ D 1) idx))))))))))))

(define (integral-basis F x y)
  (let* ((F (simplify (expand F)))
         (n (ib-ydeg F y)))
    (if (not n)
        #f
        (if (ib-unital? F y)
            (ib-basis-monic F n x y)
            (let* ((lc (simplify (coeff F y n)))
                   (z 'intbasis-z)
                   (G (expand (simplify (list '* (list '^ lc (- n 1))
                                              (subst (list (list y (list '/ z lc))) F)))))
                   (bs (ib-basis-monic G n x z)))
              (cond ((equal? bs 'unknown) 'unknown)
                    ((not bs) #f)
                    (else (map (lambda (w)
                                 (simplify (subst (list (list z (list '* lc y))) w)))
                               bs))))))))

; ---------- сертификат ----------

; характеристический многочлен элемента w над ℚ(x): Res_y(F, T·den − num)/den^n
(define (ib-charpoly F w x y)
  (let ((u (try (together w) (lambda (e) #f))))
    (if (not u)
        #f
        (let ((num (numer u)) (den (denom u)))
          (if (or (not num) (not den))
              #f
              (let* ((T 'intbasis-T)
                     (R (expand (resultant F (list '- (list '* T den) num) y)))
                     (d (try (degree R T) (lambda (e) #f)))
                     (n (ib-ydeg F y))
                     (denp (ib-poly-parse (expand (list '^ den n)) x)))
                (if (or (not d) (not denp))
                    #f
                    (let loop ((k 0) (acc '()))
                      (if (> k d)
                          (ib-trim-polys (reverse acc))
                          (let* ((ck (try (coeff R T k) (lambda (e) 0)))
                                 (cp (ib-poly-parse (expand ck) x)))
                            (if (not cp)
                                #f
                                (let ((qr (ib-p-divmod cp denp)))
                                  (if (not (ib-p-zero? (cadr qr)))
                                      #f
                                      (loop (+ k 1) (cons (car qr) acc)))))))))))))))

(define (ib-trim-polys l)
  (cond ((null? l) '())
        ((ib-p-zero? (car (reverse l))) (ib-trim-polys (reverse (cdr (reverse l)))))
        (else l)))

(define (ib-disc-of-chi chi x)
  (let* ((T 'intbasis-T)
         (e (ib-polys->expr chi T x))
         (R (try (expand (resultant e (diff T e) T)) (lambda (err) #f))))
    (if R (ib-poly-parse R x) #f)))

(define (ib-val-at p a x)
  (let loop ((p (ib-p-trim p)) (k 0))
    (if (ib-p-zero? p)
        k
        (let ((qr (ib-p-divmod p (list (- a) 1))))
          (if (ib-p-zero? (cadr qr))
              (loop (car qr) (+ k 1))
              k)))))

(define (ib-get al k)
  (let ((p (ib-assoc k al))) (if p (cadr p) #f)))

; сумма δ особых точек над a (умножаем на число сопряжённых точек группы)
(define (ib-sing-sum a F x y)
  (let ((gs (try (singular-points F x y) (lambda (e) 'unknown))))
    (if (or (equal? gs 'unknown) (null? gs))
        'unknown
        (foldl (lambda (acc g)
                 (cond ((equal? acc 'unknown) 'unknown)
                       ((equal? (car g) 'unknown) 'unknown)
                       ((not (equal? (ib-get g 'at) 'affine)) acc)
                       (else
                        (let ((px (cadr (car g))))
                          (if (and (number? px) (equal? (simplify px) a))
                              (+ acc (* (ib-get g 'delta) (ib-get g 'conjugates)))
                              acc)))))
              0 gs))))

(define (ib-cert-vals discF detP D n F x y)
  (let ((fs (try (factor-list (ib-poly->expr discF x)) (lambda (e) #f))))
    (if (not fs)
        #f
        (let ((Dp (ib-poly-parse D x)))
          (if (equal? Dp #f)
              #f
              (let loop ((fs (cdr fs)) (acc #t))
                (cond ((not acc) acc)
                      ((null? fs) acc)
                      (else
                       (let* ((f (car fs))
                              (g (car f))
                              (e (cadr f)))
                         (if (< e 2)
                             (loop (cdr fs) acc)
                             (let ((a (ib-linear-root g x)))
                               (if (equal? a 'unknown)
                                   'unknown
                                   (let ((dp (- (* n (ib-val-at Dp a x))
                                                (ib-val-at detP a x)))
                                         (ds (ib-sing-sum a F x y)))
                                     (cond ((equal? ds 'unknown)
                                            (loop (cdr fs) 'unknown))
                                           ((< dp 0) #f)
                                           ((= dp ds) (loop (cdr fs) acc))
                                           (else #f)))))))))))))))

(define (integral-basis-check-general F x y basis)
  (let* ((F (simplify (expand F)))
         (n (ib-ydeg F y)))
    (cond
      ((not n) #f)
      ((not (ib-unital? F y)) 'unknown)
      ((not (and (list? basis) (= (length basis) n))) #f)
      (else
       (let ((chis (map (lambda (w) (ib-charpoly F w x y)) basis)))
         (if (not (foldl (lambda (ok c) (and ok (not (equal? c #f)))) #t chis))
             #f
             (let ((vecs (ib-basis->vecs basis n x y))
                   (discF (ib-poly-parse (expand (resultant F (diff y F) y)) x)))
               (if (or (not vecs) (not discF))
                   #f
                   (let ((cl (ib-vecs-clear-denoms vecs n x)))
                     (if (equal? cl 'unknown)
                         #f
                         (let ((rows (car cl)) (D (cdr cl)))
                           (if (not (= (length rows) n))
                               #f
                               (ib-cert-vals discF (ib-det rows) D n F x y)))))))))))))
