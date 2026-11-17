; RUBI.INDEX: структурный индекс правил (дерево признаков образца). Тесты проверяют главное свойство
; индекса — надмножество: если правило совпало с выражением, все признаки его образца есть в выражении
; (ложноотрицательных нет), включая AC-случаи (+ и * как мультимножества) и необязательные аргументы;
; плюс что флаг выключает отсев и что rubi-index-lost на настоящих правилах пуст.
(load (string-append lib-dir "rubi/utils.lisp"))

; свой стенд (файлы тестов делят окружение — не трогаем rubi-test-setup/rubi-rule-setup)
(define (rubi-index-setup pats)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #t)
  (let loop ((l pats) (i 0))
    (if (pair? l)
        (begin (rubi::rubi-add-rule (string-append "idx-" (to-string i)) (car l) '() 'x)
               (loop (cdr l) (+ i 1)))))
  (rubi::rubi-build-index)
  (set! rubi::*rubi-index* #t))

(define (rubi-index-rules) rubi::*rubi-rules*)
(define (rubi-index-rule id) (car (filter (lambda (r) (equal? (nth r 1) id)) rubi::*rubi-rules*)))
(define (rubi-index-norm e) (ac-strip-units (ac-norm e)))
(define (rubi-index-feats p) (rubi::rubi-pat-feats (rubi-index-norm p)))
(define (rubi-index-has? atom fs) (and (member? atom fs) #t))

; совпало ли правило r с выражением e (семантика движка: подготовленный образец, явная разметка)
(define (rubi-index-match? r e)
  (let ((b (try (ac-match-prepared (rubi::rubi-prepared r) (rubi-index-norm e) #f) (lambda (err) #f))))
    (and b #t)))

; --- признаки образца ---

(deftest "rubi-index: признаки образца — жёсткая голова, степень, AC-узел"
  ; sin: голова и арность, путь от корня пуст
  (let ((fs (rubi-index-feats '(sin ?u))))
    (assert-equal 2 (length fs))
    (assert-true (rubi-index-has? '(*node* () sin 1) fs))
    (assert-true (rubi-index-has? '(*any* sin 1) fs)))
  ; степень: (*pow* путь) и показатель-число
  (let ((fs (rubi-index-feats '(^ ?u 2))))
    (assert-true (rubi-index-has? '(*pow* ()) fs))
    (assert-true (rubi-index-has? '(*pow* () 2) fs)))
  ; показатель-переменная: (*pow*) есть, конкретного показателя нет
  (let ((fs (rubi-index-feats '(^ (sin ?u) ?n))))
    (assert-true (rubi-index-has? '(*pow* ()) fs))
    (assert-true (rubi-index-has? '(*node* (^) sin 1) fs))
    (assert-equal #f (rubi-index-has? '(*pow* () 2) fs)))
  ; произведение с двумя не-переменными множителями — узел * обязателен; переменные — джокеры
  (let ((fs (rubi-index-feats '(* x (^ (+ a (* b x)) ?n)))))
    (assert-true (rubi-index-has? '(*ac* () *) fs))
    (assert-true (rubi-index-has? '(*node* (*) x 0) fs))
    (assert-true (rubi-index-has? '(*pow* (*)) fs))))

(deftest "rubi-index: джокеры и «исчезающие» узлы признаков не дают"
  ; голые переменные
  (assert-equal '() (rubi-index-feats '?u))
  (assert-equal '() (rubi-index-feats '(* ?a ?b)))
  (assert-equal '() (rubi-index-feats '(+ ?a (* ?b ?c))))
  ; (^ ?u ?n.): необязательный показатель — образец годится и не-степени (единица степени)
  (assert-equal '() (rubi-index-feats '(^ ?u ?n.)))
  ; единственный не-переменный множитель: узел * может выродиться в него — путь недостоверен,
  ; структурных признаков нет
  (let ((fs (rubi-index-feats '(* (^ x 2) ?a))))
    (assert-equal #f (rubi-index-has? '(*ac* () *) fs))
    (assert-equal #f (rubi-index-has? '(*pow* (*)) fs)))
  ; постоянное поддерево компилируется в K (сравнивается после simplify) — структуру не гарантируем
  (assert-equal '() (rubi-index-feats '(/ 1 (+ a (* b x))))))

; --- главное свойство: индекс не отсекает то, что совпало (надмножество) ---

(deftest "rubi-index: совпавшее правило всегда проходит индекс (AC, степени, необязательные аргументы)"
  (rubi-index-setup
   '((sin ?u) (^ (sin ?u) ?n) (^ ?u 2) (^ ?u ?n) (^ ?u ?n.)
     (* x (^ (+ a (* b x)) ?n)) (+ ?a (* ?b x)) (* ?a ?b)
     (* (^ (sin ?u) ?m) (^ (cos ?u) ?n)) (log (+ a (* b x)))
     (atan (* ?a ?x)) (* (^ (+ a (* b x)) 1/2) ?u) (+ ?a (?f ?u))))
  (let ((exprs '((sin x) (^ (sin x) 3) (^ x 2) x (atan x) (log (+ 2 (* 3 x)))
                 (+ a (* b x)) (* x (+ a (* b (* c x)))) (* 2 x)
                 (* (^ (sin x) 2) (^ (cos x) 3)) (* (sin x) (cos x))
                 (^ (+ a (* b x)) 1/2) (* (^ (+ a (* b x)) 1/2) c)
                 (exp (* 2 x)) (* 3 (sin x))))
        (n 0))
    (for-each
     (lambda (r)
       (for-each
        (lambda (e)
          (if (rubi-index-match? r e)
              (begin (set! n (+ n 1))
                     (assert-true (rubi::rubi-feats-ok? r (rubi::rubi-expr-feats (rubi-index-norm e)))))))
        exprs))
     (rubi-index-rules))
    ; совпадений в матрице достаточно, иначе тест ничего не проверяет
    (assert-true (> n 5))))

(deftest "rubi-index: AC — порядок и лишние множители не мешают, чужая структура отсекается"
  (rubi-index-setup '((* (^ (sin ?u) ?m) (^ (cos ?u) ?n))))
  (let* ((r (rubi-index-rule "idx-0"))
         ; те же множители в другом порядке и с лишним множителем — образец подходит
         (ok1 (rubi::rubi-feats-ok? r (rubi::rubi-expr-feats (rubi-index-norm '(* (^ (cos x) 3) (^ (sin x) 2))))))
         (ok2 (rubi::rubi-feats-ok? r (rubi::rubi-expr-feats (rubi-index-norm '(* 5 (^ (cos x) 3) (^ (sin x) 2))))))
         ; sin^(1/2) без cos — образец не подходит, и индекс это видит
         (no (rubi::rubi-feats-ok? r (rubi::rubi-expr-feats (rubi-index-norm '(^ (sin x) 1/2))))))
    (assert-equal #t ok1)
    (assert-equal #t ok2)
    (assert-equal #f no)
    (assert-equal #f (rubi-index-match? r '(^ (sin x) 1/2)))))

; --- флаг и ложные отсечения на настоящих правилах ---

(deftest "rubi-index: флаг выключает отсев"
  (rubi-index-setup '((sin ?u) (^ (sin ?u) ?n) (^ ?u 2) (^ ?u ?n) (* ?a ?b)))
  (let* ((r (rubi-index-rule "idx-0"))
         (fh (rubi::rubi-expr-feats (rubi-index-norm 'x))))
    (assert-equal #f (rubi::rubi-feats-ok? r fh))
    (unwind-protect
     (begin (set! rubi::*rubi-index* #f)
            (assert-equal #t (rubi::rubi-feats-ok? r fh)))
     (set! rubi::*rubi-index* #t))))

(deftest "rubi-index: rubi-index-lost на настоящих правилах пуст (ложных отсечений нет)"
  ; входы разных глав: алгебра, тригонометрия, квадратичный двучлен в степени, логарифм
  (rubi-index-setup '((^ ?u ?n) (* ?a ?b) (sin ?u)))
  (for-each
   (lambda (e) (assert-equal '() (rubi::rubi-index-lost (rubi-index-norm e))))
   '((^ x 2) (* x (sin x)) (log x) (* (^ x 2) (^ (+ 1 (^ x 2)) 1/2)) (tan x))))

