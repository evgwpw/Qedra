; group.lisp — перестановочные группы (шаг G1)
; Перестановка степени n — вектор образов на точках 0…n−1; ввод/вывод — циклы на точках 1…n.
; Произведение (p·q)(i) = q(p(i)) — сначала p, как в GAP.
; Группа — список образующих и степень n.
(module group
  (export perm-mul perm-inv perm-order perm-sign perm-from-cycles perm->cycles perm-identity? perm-id
          group-orbit group-stabilizer-gens group-bsgs group-order group-member? bsgs-check
          cube-move all-fix? all-member?
          group-cosets group-index group-subgroup?
          symmetric-group alternating-group dihedral-group cyclic-group
          coset-enumerate coset-table-check))

; ---------- вспомогательное ----------

(define (upto a b)
  (if (> a b) '() (cons a (upto (+ a 1) b))))

(define (all-pred? f lst)
  (cond ((null? lst) #t)
        ((f (car lst)) (all-pred? f (cdr lst)))
        (else #f)))

(define (any-pred? f lst)
  (cond ((null? lst) #f)
        ((f (car lst)) #t)
        (else (any-pred? f (cdr lst)))))

; ---------- вспомогательное для тестов и кубика ----------

; все перестановки списка фиксируют точку pt (0-based)?
(define (all-fix? ps pt)
  (all-pred? (lambda (p) (= (vref p pt) pt)) ps))

; все перестановки списка — члены группы G?
(define (all-member? G ps)
  (all-pred? (lambda (p) (group-member? G p)) ps))


; ---------- элементарные операции ----------

; растянуть перестановку до степени m (доп. точки фиксированы)
(define (perm-pad p m)
  (let ((np (length p)))
    (if (>= np m) p
        (let ((v (perm-id m)))
          (let loop ((i 0))
            (if (= i np) v (begin (vset! v i (vref p i)) (loop (+ i 1)))))))))
(define (perm-mul p q)
  ; степени могут отличаться — расширяем обе до общей
  (let* ((m (max (length p) (length q)))
         (pp (perm-pad p m))
         (qq (perm-pad q m)))
    (vector-map (lambda (x) (vref qq x)) pp)))

(define (perm-inv p)
  (let ((n (length p)) (r (make-vector (length p) 0)))
    (let loop ((i 0))
      (if (= i n) r
          (begin (vset! r (vref p i) i) (loop (+ i 1)))))))

(define (perm-identity? p)
  (let ((n (length p)))
    (let loop ((i 0))
      (cond ((= i n) #t)
            ((= (vref p i) i) (loop (+ i 1)))
            (else #f)))))

(define (perm-id n)
  (let ((v (make-vector n 0)))
    (let loop ((i 0)) (if (= i n) v (begin (vset! v i i) (loop (+ i 1)))))))

; знак: (−1)^(n − число циклов)
(define (perm-sign p)
  (let* ((n (length p))
         (seen (make-vector n #f))
         (cycles (let loop ((i 0) (c 0))
                   (cond ((= i n) c)
                         ((vref seen i) (loop (+ i 1) c))
                         (else
                          (let walk ((j i))
                            (if (vref seen j) #f
                                (begin (vset! seen j #t) (walk (vref p j)))))
                          (loop (+ i 1) (+ c 1)))))))
    (if (even? (- n cycles)) 1 -1)))
(define (perm->cycles p)
  (let* ((n (length p))
         (seen (make-vector n #f))
         (out ()))
    (let loop ((i 0))
      (cond ((= i n) (reverse out))
            ((or (vref seen i) (= (vref p i) i)) (loop (+ i 1)))
            (else
             (let ((cyc ()))
               (let walk ((j i))
                 (if (vref seen j) #f
                     (begin (vset! seen j #t)
                            (set! cyc (cons (+ j 1) cyc))
                            (walk (vref p j)))))
               (set! out (cons (reverse cyc) out))
               (loop (+ i 1))))))))

(define (perm-from-cycles cycles)
  (let* ((n (foldl (lambda (acc c) (foldl (lambda (a pt) (max a pt)) acc c)) 1 cycles))
         (p (perm-id n)))
    (for-each (lambda (c)
                (let ((m (length c)))
                  (let loop ((k 0))
                    (if (= k m) #f
                        (begin
                         (vset! p (- (nth c k) 1) (- (nth c (modulo (+ k 1) m)) 1))
                         (loop (+ k 1)))))))
              cycles)
    p))



(define (perm-order p)
  (foldl lcm 1 (map length (perm->cycles p))))

; ---------- орбиты и стабилизаторы ----------


; орбита точки pt (0-based) под gens; дерево Шрайера: tree[γ] = (γ' . g), g(γ') = γ
(define (group-orbit-tree gens pt)
  (let* ((m (foldl (lambda (a g) (max a (length g))) 1 gens))
         (gens (map (lambda (g) (perm-pad g m)) gens))
         (seen (make-hash))
         (tree (make-hash)))
    (hash-set! seen pt #t)
    ; BFS: очередь — список, обрабатываем голову, новые точки в хвост
    (let loop ((queue (list pt)) (orbit (list pt)))
      (if (null? queue)
          (cons (reverse orbit) tree)
          (let ((cur (car queue)))
            (let inner ((gs gens) (q (cdr queue)) (orb orbit))
              (if (null? gs)
                  (loop q orb)
                  (let* ((g (car gs))
                         (img (vref g cur)))
                    (if (hash-ref seen img)
                        (inner (cdr gs) q orb)
                        (begin (hash-set! seen img #t)
                               (hash-set! tree img (cons cur g))
                               (inner (cdr gs) (append q (list img)) (cons img orb))))))))))))

(define (group-orbit gens pt)
  (map (lambda (i) (+ i 1)) (car (group-orbit-tree gens (- pt 1)))))

; шрайеровские образующие стабилизатора точки b: s = u(γ)·g·u(γ^g)^−1 — фиксируют b
; (конвенция произведения (p·q)(i) = q(p(i)); u(δ) переводит b−1 в δ; γ^g = образ γ под g)
(define (schreier-gens sgs orb trans)
  (let* ((m (foldl (lambda (a g) (max a (length g))) 1 sgs))
         (sgs (map (lambda (g) (perm-pad g m)) sgs))
         (acc '()))
    (for-each (lambda (g)
                (for-each (lambda (gamma)
                            (let ((s (perm-mul (perm-mul (hash-ref trans gamma) g)
                                               (perm-inv (hash-ref trans (vref g gamma))))))
                              (if (not (perm-identity? s))
                                  (set! acc (cons s acc)))))
                          orb))
              sgs)
    acc))

; u-перестановки по дереву: trans[δ] переводит b−1 в δ;
; путь b → … → δ: предок встречается раньше, метки перемножаются СЛЕВА (g_next·…·g_first)
(define (build-trans b tree orbit n)
  (let ((trans (make-hash)))
    (for-each (lambda (d)
                (hash-set! trans d
                           (let loop ((dd d) (w (perm-id n)))
                             (if (= dd (- b 1))
                                 w
                                 (let ((e (hash-ref tree dd #f)))
                                   (loop (car e) (perm-mul (cdr e) w)))))))
              orbit)
    trans))

; образующие стабилизатора точки pt (1-based) — лемма Шрайера
(define (group-stabilizer-gens gens pt)
  (let* ((res (group-orbit-tree gens (- pt 1)))
         (orbit (car res))
         (tree (cdr res))
         (n (foldl (lambda (a g) (max a (length g))) 1 gens))
         (trans (build-trans pt tree orbit n)))
    (schreier-gens gens orbit trans)))

; ---------- Шрайер — Симс (детерминированный, с просеиванием) ----------

; уровень BSGS: (b sgs orbit trans); sgs — сильные образующие уровня (фиксируют base[0..i−1])
(define (bsgs-level b sgs)
  (let* ((res (group-orbit-tree sgs (- b 1)))
         (orbit (car res))
         (tree (cdr res))
         (n (foldl (lambda (a g) (max a (length g))) 1 sgs))
         (trans (build-trans b tree orbit n)))
    (list b sgs orbit trans)))

; просеивание p по списку уровней: остаток после снятия всех уровней
(define (levels-sift levels p)
  (let ((r p))
    (let loop ((lv levels))
      (if (or (null? lv) (not r))
          r
          (let* ((lvl (car lv)) (b (nth lvl 0)) (trans (nth lvl 3)))
            (let ((u (hash-ref trans (vref r (- b 1)) #f)))
              (if (not u)
                  #f
                  (begin (set! r (perm-mul r (perm-inv u)))
                         (loop (cdr lv))))))))))

; добавить новый уровень для точки базы moved и вернуть (base levels)
(define (bsgs-extend base levels moved sgs)
  (let* ((b (+ moved 1))
         (lvl (bsgs-level b sgs)))
    (list (append base (list b)) (append levels (list lvl)))))

; дедупликация списка перестановок (по значению)
(define (perm-dedup ps)
  (let ((h (make-hash)) (acc '()))
    (for-each (lambda (p)
                (let ((k (vector->list p)))
                  (if (not (hash-ref h k #f))
                      (begin (hash-set! h k #t) (set! acc (cons p acc))))))
              ps)
    (reverse acc)))

; детерминированный Шрайер — Симс (сверху вниз, Holt гл. 4):
; уровень 1 — по всем генераторам; уровень i+1 — по шрайеровским генераторам
; уровня i (лемма Шрайера: они порождают стабилизатор β_i), отфильтрованным от
; тождественных и дубликатов (фильтр Чейна/Симса).
(define (group-bsgs gens n)
  (let ((gens (map (lambda (g) (perm-pad g n))
                   (filter (lambda (g) (not (perm-identity? g))) gens))))
    (if (null? gens)
        (list '() '())
        (let ((base '()) (levels '()))
          (let extend ((sgs gens))
            (if (null? sgs)
                #f
                (let* ((pt (let loop ((k 0))
                             (if (= (vref (car sgs) k) k) (loop (+ k 1)) k)))
                       (b (+ pt 1))
                       (lvl (bsgs-level b sgs))
                       (stab (perm-dedup (schreier-gens (nth lvl 1) (nth lvl 2) (nth lvl 3)))))
                  (set! base (append base (list b)))
                  (set! levels (append levels (list lvl)))
                  (extend stab))))
          (list base levels)))))



(define (group-order G)
  (let* ((gens (car G)) (n (cadr G))
         (bsgs (group-bsgs gens n)))
    (foldl * 1 (map (lambda (lvl) (length (nth lvl 2))) (cadr bsgs)))))

; просеивание p по BSGS: остаток (тождество — член); #f — образ вне орбиты
(define (bsgs-sift bsgs p)
  (let ((base (car bsgs)) (levels (cadr bsgs)) (r p))
    (let loop ((i 0))
      (if (= i (length base))
          r
          (let* ((lvl (nth levels i)) (b (nth lvl 0)) (trans (nth lvl 3)))
            (let ((img (vref r (- b 1))))
              (let ((u (hash-ref trans img #f)))
                (if (not u)
                    #f
                    (begin (set! r (perm-mul r (perm-inv u)))
                           (loop (+ i 1)))))))))))

(define (group-member? G p)
  (let* ((gens (car G)) (n (cadr G))
         (bsgs (group-bsgs gens n))
         (r (bsgs-sift bsgs p)))
    (and r (perm-identity? r))))

; ---------- сертификат BSGS ----------

; 1) каждый сильный образующий уровня i фиксирует base[0..i−1];
; 2) каждый шрайеровский образующий каждого уровня просеивается до тождества
; (полная проверка, не случайная). Второй аргумент — готовая система или #f (построить);
; для проверки подделок: убрать один сильный образующий → порядок занижен → #f
(define (bsgs-check G given)
  (let* ((gens (car G)) (n (cadr G))
         (bsgs (if given given (group-bsgs gens n)))
         (base (car bsgs)) (levels (cadr bsgs)))
    (and
     ; замечание ревью G1.1): ⟨S⟩ = ⟨gens⟩ — каждый образующий G просеивается по системе (иначе BSGS
     ; подгруппы, например A5 для S5, проходил), и каждый сильный образующий лежит в G (проверка
     ; принадлежности через собственную систему G — не независима, но ловит BSGS надгруппы)
     (all-pred? (lambda (g) (let ((r (try (bsgs-sift bsgs g) (lambda (e) #f)))) (and r (perm-identity? r)))) gens)
     (or (not given)
         (all-pred? (lambda (lvl) (all-pred? (lambda (s) (group-member? G s)) (nth lvl 1))) levels))
     (let loop ((i 0))
       (if (= i (length levels))
           #t
           (let ((lvl (nth levels i)))
             (and (all-pred? (lambda (g)
                               (all-pred? (lambda (j) (= (vref g (- (nth base j) 1)) (- (nth base j) 1)))
                                          (upto 0 (- i 1))))
                             (nth lvl 1))
                  (loop (+ i 1))))))
     (let loop ((i 0))
       (if (= i (length levels))
           #t
           (let* ((lvl (nth levels i))
                  (sgs (nth lvl 1)) (b (nth lvl 0))
                  (stab (group-stabilizer-gens sgs b)))
             (and (all-pred? (lambda (s)
                               (let ((r (try (bsgs-sift bsgs s) (lambda (e) #f)))) (and r (perm-identity? r))))
                             stab)
                  (loop (+ i 1)))))))))
; поворот грани кубика: 24 точки = 8 углов × 3 ориентации, индекс 3p+o;
; cycles — цикл позиций углов (1-based), deltas — приращение ориентации
; в позиции-приёмнике (kociemba co)
(define (cube-move cycles deltas)
  (let ((p (perm-id 24)))
    (for-each (lambda (c)
                (let ((m (length c)))
                  (let loop ((k 0))
                    (if (= k m) #f
                        (let* ((src (- (nth c k) 1))
                               (dst (- (nth c (modulo (+ k 1) m)) 1))
                               (d (nth deltas src)))
                          (let lo ((o 0))
                            (if (= o 3) #f
                                (begin (vset! p (+ (* 3 src) o)
                                             (+ (* 3 dst) (modulo (+ o d) 3)))
                                       (lo (+ o 1)))))
                          (loop (+ k 1)))))))
              cycles)
    p))

; ---------- G1.2: смежные классы и стандартные группы ----------

; H ≤ G? — каждый образующий H принадлежит G
(define (group-subgroup? G H)
  (and (= (cadr G) (cadr H))
       (all-pred? (lambda (h) (group-member? G h)) (car H))))

; правые смежные классы H\G: список представителей (BFS по образующим G,
; принадлежность классу H·r ⇔ x·r⁻¹ ∈ H). Возвращает список представителей
; либо 'not-subgroup.
(define (group-cosets G H)
  (if (not (group-subgroup? G H))
      'not-subgroup
      (let* ((gens (car G)) (n (cadr G))
             (e (perm-id n))
             (reps (list e))
             ; x относится к классу с представителем r ⇔ x·r⁻¹ ∈ H
             (in-class? (lambda (x r) (group-member? H (perm-mul x (perm-inv r)))))
             (find-rep (lambda (x)
                         (let loop ((rs reps))
                           (cond ((null? rs) #f)
                                 ((in-class? x (car rs)) (car rs))
                                 (else (loop (cdr rs))))))))
        (let loop ((queue (list e)))
          (if (null? queue)
              reps
              (let ((r (car queue)))
                (for-each (lambda (g)
                            (let* ((x (perm-mul r g))
                                   (hit (find-rep x)))
                              (if (not hit)
                                  (begin (set! reps (append reps (list x)))
                                         (set! queue (append queue (list x)))))))
                          gens)
                (loop (cdr queue))))))))

; индекс [G:H] = |G|/|H| (через BSGS-порядки; H ≤ G — иначе #f)
(define (group-index G H)
  (if (not (group-subgroup? G H))
      #f
      (quotient (group-order G) (group-order H))))

; ---------- G1.2: стандартные группы ----------

; S_n: (1 2) и (1 2 … n) порождают (n ≥ 2)
(define (symmetric-group n)
  (if (< n 2)
      (list '() n)
      (list (list (perm-from-cycles '((1 2)))
                  (perm-from-cycles (list (upto 1 n))))
            n)))

; A_n: (1 2 3) и (1 2 … n) порождают при чётном... стандартно: (1 2 3) и циклы (1 2 … n)
; при n чётном (нечётный цикл — чётная перестановка), при n нечётном нужен (2 3 … n).
; Надёжно: (1 2 3) и (1 2)(3 4 … n): 3-цикл и (n−2)-цикл при n чётном; универсально
; берём (1 2 3) и (1 2 … n) при n нечётном, (1 2 3) и (2 3 … n) при n чётном.
(define (alternating-group n)
  (cond ((< n 3) (list '() n))
        ((= n 3) (list (list (perm-from-cycles '((1 2 3)))) n))
        ((odd? n) (list (list (perm-from-cycles '((1 2 3)))
                              (perm-from-cycles (list (upto 1 n))))
                        n))
        (else (list (list (perm-from-cycles '((1 2 3)))
                          (perm-from-cycles (list (upto 2 n))))
                    n))))

; D_n на n точках (порядок 2n): r = (1 … n), s = отражение (2 n)(3 n−1)…
(define (dihedral-group n)
  (if (< n 3)
      (symmetric-group n)
      (let* ((r (perm-from-cycles (list (upto 1 n))))
             (s (perm-id n)))
        (let loop ((k 2))
          (if (> k (quotient (+ n 1) 2))
              #f
              (begin (vset! s (- k 1) (- (+ n 1) k))
                     (vset! s (- (+ n 1) k) (- k 1))
                     (loop (+ k 1)))))
        (list (list r s) n))))

; C_n: (1 2 … n)
(define (cyclic-group n)
  (if (< n 2)
      (list '() n)
      (list (list (perm-from-cycles (list (upto 1 n)))) n)))

; ---------- G1.2: Тодд — Коксетер (HLT с фикспоинтом) ----------

; буква слова: (g . +1) для символа g, (g . −1) для (inv g)
(define (tc-letter x)
  (if (pair? x) (cons (cadr x) -1) (cons x 1)))

(define (tc-word w) (map tc-letter w))

(define (tc-inv-letter L) (cons (car L) (- (cdr L))))

(define (tc-find parent c)
  (let ((p (vref parent c)))
    (if (= p c)
        c
        (let ((r (tc-find2 parent p 0)))
          (begin (vset! parent c r) r)))))

(define (tc-find2 parent c n)
  (if (> n 1000)
      c
      (let ((p (vref parent c)))
        (if (= p c) c (tc-find2 parent p (+ n 1))))))

(define (tc-union! parent a b)
  (let ((ra (tc-find parent a)) (rb (tc-find parent b)))
    (if (= ra rb)
        #f
        ; класс 0 всегда остаётся корнем (представитель подгруппы)
        (if (or (= ra 0) (= rb 0))
            (begin (vset! parent (max ra rb) 0) #t)
            (begin (vset! parent ra rb) #t)))))

; coset-enumerate gens rels sub-gens max-cosets →
;   (list :index N :table tbl) — tbl: хеш (g . 1) → вектор классов (канонические),
;   либо 'unknown при превышении max-cosets.
; Слова: списки букв a / (inv a). Правые классы, буква действует справа: c --g--> c^g.
(define (coset-enumerate gens rels sub-gens max-cosets)
  (let* ((rels (map tc-word rels))
         (sub-gens (map tc-word sub-gens))
         (fwd (apply append (map (lambda (g) (list (cons g 1) (cons g -1))) gens)))
         (cap (+ (* 3 max-cosets) 32))
         (table (make-hash))
         (parent (make-vector cap 0))
         (ncos 1)
         (queue '())
         (overflow? #f))
    (for-each (lambda (b) (hash-set! table b (make-vector cap -1))) fwd)
    ; канонический корень класса
    (define (find c) (tc-find parent c))
    ; слот для нового класса — только свежий номер (переиспользование мёртвых
    ; слотов опасно: старые записи таблицы могут ссылаться на номер)
    (define (fresh-slot)
      (if (>= ncos cap) #f ncos))
    (define (define-arrow b c)
      (let ((s (fresh-slot)))
        (if (not s)
            (set! overflow? #t)
            (let ((ib (tc-inv-letter b)))
              (vset! (hash-ref table b) c s)
              (vset! (hash-ref table ib) s c)
              (vset! parent s s)
              (set! ncos (+ s 1))))))
    ; провести слово w от класса c; конечный класс
    (define (trace w c)
      (let loop ((ww w) (cc c))
        (if (null? ww)
            cc
            (let* ((b (car ww))
                   (tv (hash-ref table b))
                   (d (vref tv cc)))
              (cond ((and (= d -1) overflow?) cc)
                    ((= d -1) (begin (define-arrow b cc)
                                     (if overflow?
                                         cc
                                         (loop (cdr ww) (vref (hash-ref table b) cc)))))
                    (else (loop (cdr ww) (find d))))))))
    ; активные классы (канонические)
    (define (active-cosets)
      (let loop ((c 0) (acc '()))
        (if (= c ncos)
            (reverse acc)
            (if (= (find c) c)
                (loop (+ c 1) (cons c acc))
                (loop (+ c 1) acc)))))
    ; коинциденция: объединить классы a и b (класс 0 всегда представитель);
    ; строки таблицы представителей объединить; новые совпадения — в очередь
    (define (coincide a b)
      (let ((ra (find a)) (rb (find b)))
        (if (not (= ra rb))
            (let ((rep (cond ((= ra 0) 0) ((= rb 0) 0) (else (min ra rb))))
                  (dead (cond ((= ra 0) rb) ((= rb 0) ra) (else (max ra rb)))))
              (vset! parent dead rep)
              ; объединить строки: rep-строка получает все известные стрелки dead-строки
              (for-each (lambda (bb)
                          (let ((ta (vref (hash-ref table bb) rep))
                                (td (vref (hash-ref table bb) dead)))
                            (cond ((and (= ta -1) (>= td 0))
                                   (vset! (hash-ref table bb) rep (find td)))
                                  ((and (= ta -1) (= td -1)) #f)
                                  ((and (>= ta 0) (= td -1)) #f)
                                  (else
                                   (if (not (= (find ta) (find td)))
                                       (set! queue (cons (cons ta td) queue)))))))
                        fwd))
            #f)))
    (define (process-queue)
      (let loop ()
        (if (null? queue)
            #f
            (let ((p (car queue)))
              (set! queue (cdr queue))
              (coincide (car p) (cdr p))
              (loop)))))
    ; полный проход: rels из каждого активного класса, sub-gens из 0
    (define (scan-all)
      (for-each (lambda (w)
                  (for-each (lambda (c)
                              (let ((e (trace w c)))
                                (if (and (not overflow?) (not (= e (find c))))
                                    (begin (coincide e c) (process-queue)))))
                            (active-cosets)))
                rels)
      (for-each (lambda (w)
                  (let ((e (trace w 0)))
                    (if (and (not overflow?) (not (= e 0)))
                        (begin (coincide e 0) (process-queue)))))
                sub-gens))
    ; замечание ревью G1.2): образующий, не входящий в соотношения, никогда не определялся при
    ; сканировании — таблица оставалась неполной (⟨a | ⟩ давал индекс 1, ⟨a, b | a²⟩ — 2). После
    ; стабилизации определяем недостающую стрелку и сканируем снова; бесконечный индекс → переполнение.
    (define (undefined-arrow)
      (let loop ((cs (active-cosets)))
        (if (null? cs)
            #f
            (let inner ((bs fwd))
              (cond ((null? bs) (loop (cdr cs)))
                    ((= (vref (hash-ref table (car bs)) (car cs)) -1) (cons (car bs) (car cs)))
                    (else (inner (cdr bs))))))))
    (let loop ((iter 0))
      (if (or overflow? (> iter 100000))
          #f
          (let ((before (length (active-cosets))))
            (scan-all)
            (cond (overflow? #f)
                  ((not (= (length (active-cosets)) before)) (loop (+ iter 1)))
                  (else
                   (let ((ua (undefined-arrow)))
                     (if ua
                         (begin (define-arrow (car ua) (cdr ua)) (loop (+ iter 1)))
                         #f)))))))
    (if (or overflow? (not (null? queue)) (undefined-arrow))
        'unknown
        (let* ((live (active-cosets))
               (renum (make-hash))
               (idx 0))
          (for-each (lambda (c) (begin (hash-set! renum c idx) (set! idx (+ idx 1)))) live)
          (if (> idx max-cosets)
              'unknown
              (let ((tbl (make-hash)))
                (for-each (lambda (g)
                            (hash-set! tbl g
                                       (let ((tv (hash-ref table (cons g 1)))
                                             (v (make-vector idx -1)))
                                         (let loop ((k 0))
                                           (if (= k idx)
                                               v
                                               (let ((d (vref tv (nth live k))))
                                                 (if (= d -1)
                                                     #f
                                                     (vset! v k (hash-ref renum (find d) -1)))
                                                 (loop (+ k 1))))))))
                          gens)
                (list :index idx :table tbl)))))))
; сертификат TC: таблица полна, столбцы — перестановки, действие транзитивно, каждое rel замыкается
; из каждого класса, каждое sub-gen слово стабилизирует класс 0. res — результат coset-enumerate.
; Доказывает: задано транзитивное действие G на idx классах с H ≤ Stab(0), т. е. [G : H] ≥ idx;
; равенство [G : H] = idx — ещё H = Stab(0) (образующие Шрайера стабилизатора в H), это не проверяется.
(define (tc-orbit-size tbl gens idx)
  (let ((seen (make-hash)))
    (hash-set! seen 0 #t)
    (let loop ((front (list 0)) (n 1))
      (if (null? front)
          n
          (let* ((c (car front))
                 (new (filter (lambda (d) (and (>= d 0) (not (hash-ref seen d #f))))
                              (map (lambda (g) (vref (hash-ref tbl g) c)) gens))))
            (for-each (lambda (d) (hash-set! seen d #t)) new)
            (loop (append (cdr front) (tc-uniq new)) (+ n (length (tc-uniq new)))))))))
(define (tc-uniq l)
  (if (null? l) '() (cons (car l) (tc-uniq (filter (lambda (x) (not (= x (car l)))) (cdr l))))))
(define (coset-table-check gens rels sub-gens res)
  (if (not (and (pair? res) (equal? (car res) :index)))
      #f
      (let* ((tbl (nth res 3))
             (idx (nth res 1))
             (trace1 (lambda (w c)
                       (let loop ((ww (map tc-letter w)) (cc c))
                         (if (null? ww)
                             cc
                             (let* ((b0 (car ww))
                                    (b (if (= (cdr b0) 1) b0 (tc-inv-letter b0)))
                                    (v (hash-ref tbl (car b) #f)))
                               (if (not v) #f (loop (cdr ww) (vref v cc)))))))))
        (and
         ; полнота: каждый генератор переводит каждый класс в класс 0..idx−1
         (all-pred? (lambda (g)
                      (let ((v (hash-ref tbl g #f)))
                        (and v (all-pred? (lambda (k) (and (>= (vref v k) 0) (< (vref v k) idx)))
                                          (upto 0 (- idx 1))))))
                    gens)
         ; каждый столбец — перестановка классов (иначе обратные не определены)
         (all-pred? (lambda (g)
                      (let ((v (hash-ref tbl g #f)) (seen (make-hash)))
                        (and v (all-pred? (lambda (k) (let ((d (vref v k)))
                                                        (if (hash-ref seen d #f) #f
                                                            (begin (hash-set! seen d #t) #t))))
                                          (upto 0 (- idx 1))))))
                    gens)
         ; транзитивность: орбита класса 0 — все классы
         (= idx (tc-orbit-size tbl gens idx))
         ; rels замыкаются из каждого класса
         (all-pred? (lambda (w)
                      (all-pred? (lambda (c) (= (trace1 w c) c)) (upto 0 (- idx 1))))
                    rels)
         ; sub-gens стабилизируют класс 0
         (all-pred? (lambda (w) (= (trace1 w 0) 0)) sub-gens)))))
