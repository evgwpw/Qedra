; set.lisp — конечные множества (Шаг 16)
;
; Представление: (make-object 'set вектор) — элементы ОТСОРТИРОВАНЫ по orderp и без дублей (equal?).
; Благодаря канонической форме равенство множеств — обычное (equal? A B), порядок аргументов не важен.
; Элементы — любые выражения (числа, символы, списки-выражения, другие множества).
; Печать: {1, 2, x}, пустое — {}.
;
; Обобщённые операции (in?, subset?) диспетчеризуются по типам аргументов через defmethod:
; (defmethod in? (any set) (x s) ...) — сигнатура = типы (элемент, контейнер).
; Принадлежность и подмножество — ТРЁХЗНАЧНЫЕ (#t / #f / unknown), см. logic.lisp.

; Шаг 21h': модуль set. Тип set (deftype) — глобальный; методы in? / subset? / print / math-print — записи глобальных таблиц
(module set
  (export set? set->list list->set set card empty-set? union set-intersection intersection set-difference
          set-map set-filter power-set in? subset? dispatch-method))

(deftype 'set 'any)

(define (set? x) (and (object? x) (equal? (object-type x) 'set)))

; внутренний конструктор: l уже отсортирован и без дублей
(define (set-raw l) (make-object 'set (list->vector l)))
(define (set->list s)
  (if (set? s) (vector->list (object-ref s 0)) (error "set->list: ожидается множество, получено" s)))

; вставка в отсортированный список без дублей: порядок orderp, дубль — по equal?
(define (set-insert x l)
  (cond ((null? l) (list x))
        ((equal? x (car l)) l)
        ((not (orderp (car l) x)) (cons x l))      ; x строго меньше (car l)
        (else (cons (car l) (set-insert x (cdr l))))))

(define (list->set l) (set-raw (foldl (lambda (acc x) (set-insert x acc)) '() l)))
(define (set &rest elems) (list->set elems))

(define (card s) (vlength (object-ref s 0)))
(define (empty-set? s) (= (card s) 0))

; --- Алгебра множеств ---

(define (set-lists sets) (map set->list sets))

; (union a b ...) — объединение; (union) — пустое множество
(define (union &rest sets) (list->set (apply append (set-lists sets))))

; (set-intersection a b ...) — пересечение множеств
(define (set-has? x l) (any? (lambda (e) (equal? x e)) l))
(define (set-intersection2 a b)
  (set-raw (filter (lambda (x) (set-has? x (set->list b))) (set->list a))))
(define (set-intersection &rest sets)
  (if (null? sets) (error "intersection: нужен хотя бы один аргумент") (foldl set-intersection2 (car sets) (cdr sets))))

; (intersection a b ...) — множества; интервалы и домены — см. domain.lisp (intersect-general)
; WASM.6a Д7: множество ∩ интервал/домен — элементы множества, лежащие в континууме
(define (set-in-filter s c)
  (let ((l (set->list s)))
    (if (any? (lambda (x) (equal? (in? x c) 'unknown)) l)
        (error "intersection: принадлежность элемента множества не решена" l)
        (set-raw (filter (lambda (x) (equal? (in? x c) #t)) l)))))

(define (intersect-any a b)
  (cond ((and (set? a) (set? b)) (set-intersection2 a b))
        ((and (set? a) (or (interval? b) (domain? b))) (set-in-filter a b))
        ((and (or (interval? a) (domain? a)) (set? b)) (set-in-filter b a))
        (else (intersect-general a b))))

(define (intersection &rest args)
  (if (every? set? args)
      (apply set-intersection args)
      (foldl intersect-any (car args) (cdr args))))

; (set-difference a b) — элементы a, которых нет в b (по equal?)
(define (set-difference a b)
  (set-raw (filter (lambda (x) (not (set-has? x (set->list b)))) (set->list a))))

; (set-map f s) — образ множества (дубли сливаются); (set-filter p s) — элементы, для которых p истинно
(define (set-map f s) (list->set (map f (set->list s))))
(define (set-filter p s) (set-raw (filter p (set->list s))))

; (power-set s) — множество всех подмножеств: 2^n элементов
(define (power-list l)
  (if (null? l)
      (list '())
      (let ((rest (power-list (cdr l))))
        (append rest (map (lambda (sub) (cons (car l) sub)) rest)))))
(define (power-set s) (list->set (map set-raw (power-list (set->list s)))))

; --- Обобщённая диспетчеризация ---

(define (dispatch-method op types)
  (let ((m (find-method op types)))
    (if (null? m)
        (error (string-append (to-string op) ": нет метода для типов") types)
        m)))

; (in? x S) — принадлежность (трёхзначная): метод (in? (any тип-S)); методы для domain/interval — domain.lisp
(define (in? x s) ((dispatch-method 'in? (list 'any (type-of s))) x s))

; (subset? a b) — включение (трёхзначное): метод по типам обоих аргументов
(define (subset? a b) ((dispatch-method 'subset? (list (type-of a) (type-of b))) a b))

; числа равны по значению (1 и 1.0 — один и тот же элемент для принадлежности)
(define (elem-equal? a b) (or (equal? a b) (and (number? a) (number? b) (= a b))))

; x ∈ множество: структурно равен элементу → #t; x и все элементы — числа и совпадений нет → #f;
; иначе (символы/выражения могут оказаться равны) → unknown. Пустое множество: всегда #f
(defmethod in? (any set) (x s)
  (let ((l (set->list s)))
    (cond ((any? (lambda (e) (elem-equal? x e)) l) #t)
          ((null? l) #f)
          ((and (number? x) (every? number? l)) #f)
          (else unknown))))

; A ⊆ B для конечного A: И (Клини) по принадлежности элементов A в B.
; Для символьных элементов результат может быть unknown (например {x} ⊆ {y}); {} ⊆ любому — #t
(defmethod subset? (set any) (a b)
  (and3-all (map (lambda (x) (in? x b)) (set->list a))))

; --- Печать ---

(define (set-string s conv)
  (if (empty-set? s)
      "{}"
      (string-append "{" (join-strings (map conv (set->list s)) ", ") "}")))

(defmethod print (set) (s) (set-string s to-string))
(defmethod math-print (set) (s) (set-string s math-print))
