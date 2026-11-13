; Lisp-тесты шага GB.Q: деление на набор с частными и сертификат идеала (lib\groebner.lisp).
; Инвариант: f = Σ qi·gi + r (проверяется expand), остаток не делится на старшие мономы.

(define (gbq-sum qs gs) (cons '+ (cons 0 (map2 (lambda (q g) (list '* q g)) qs gs))))
(define (gbq-identity? f gs vars &rest ord)
  (let* ((res (if (null? ord) (normal-form-with-quotients f gs vars) (normal-form-with-quotients f gs vars (car ord)))))
    (equal? (expand (list '- (list '+ (car res) (gbq-sum (cadr res) gs)) f)) 0)))

(deftest "groebner-quot: один делитель — обычное деление"
  (assert-equal (normal-form-with-quotients '(- (^ x 3) 1) '((- x 1)) '(x)) '(0 ((+ 1 x (^ x 2)))))
  (assert-equal (normal-form-with-quotients '(+ (^ x 2) 1) '((- x 1)) '(x)) '(2 ((+ 1 x)))))

(deftest "groebner-quot: два делителя, остаток ненулевой"
  (let ((gs '((- (* x y) 1) (- (^ y 2) 1))))
    (assert-equal (normal-form-with-quotients '(+ (^ x 2) (* x y) (^ y 2)) gs '(x y)) '((+ 2 (^ x 2)) (1 1)))
    (assert-true (gbq-identity? '(+ (^ x 2) (* x y) (^ y 2)) gs '(x y)))))

(deftest "groebner-quot: нестандартный делитель (старший коэффициент не 1)"
  (let ((gs '((- (* 2 x) 4))))
    (assert-equal (normal-form-with-quotients '(- (^ x 2) 4) gs '(x)) '(0 ((+ 1 (* 1/2 x)))))
    (assert-true (gbq-identity? '(+ (^ x 3) 5) gs '(x)))))

(deftest "groebner-quot: атом корня s^2 = 1 - x^2, обратный атом iu*s = 1"
  ; числитель F' - f после замены корня атомами: s^3 + s*x^2 - s + x*s*iu - x = s*h1 + x*h2
  (let* ((gs '((- (+ (^ s 2) (^ x 2)) 1) (- (* s iu) 1)))
         (num '(- (+ (^ s 3) (* s (^ x 2)) (* x s iu)) s x))
         (qs (ideal-certificate num gs '(s iu x))))
    (assert-equal qs '(s x))
    (assert-equal (expand (list '- (gbq-sum qs gs) num)) 0)
    ; s + x^2*iu - iu лежит в идеале, но gs не базис Грёбнера: деление честно не даёт сертификата
    (assert-equal (ideal-certificate '(- (+ s (* (^ x 2) iu)) iu) gs '(s iu x)) #f)))

(deftest "groebner-quot: тригонометрия sn^2 + cs^2 - 1"
  ; sin^3 + sin*cos^2 - sin = sin * (sn^2 + cs^2 - 1)
  (let* ((gs '((- (+ (^ sn 2) (^ cs 2)) 1)))
         (f '(- (+ (^ sn 3) (* sn (^ cs 2))) sn))
         (qs (ideal-certificate f gs '(sn cs))))
    (assert-equal qs '(sn))
    (assert-true (gbq-identity? f gs '(sn cs)))))

(deftest "groebner-quot: не элемент идеала — сертификата нет, остаток честный"
  (let ((gs '((- (+ (^ sn 2) (^ cs 2)) 1))))
    (assert-equal (ideal-certificate '(+ sn cs) gs '(sn cs)) #f)
    (assert-equal (car (normal-form-with-quotients '(+ sn cs) gs '(sn cs))) '(+ cs sn))
    (assert-equal (ideal-certificate '(+ (^ iu 1) 1) '((- (* s iu) 1)) '(s iu)) #f)))

(deftest "groebner-quot: подделка коэффициента ловится проверкой суммы"
  (let* ((gs '((- (+ (^ s 2) (^ x 2)) 1) (- (* s iu) 1)))
         (num '(- (+ (^ s 3) (* s (^ x 2)) (* x s iu)) s x))
         (bad (list 's '(* 2 x))))
    (assert-true (not (equal? (expand (list '- (gbq-sum bad gs) num)) 0)))))

(deftest "groebner-quot: порядки lex и grevlex дают корректные тождества"
  (let ((gs '((- (^ x 2) y) (- (* x y) 1)))
        (f '(+ (^ x 4) (* x y) (^ y 2))))
    (assert-true (gbq-identity? f gs '(x y) 'lex))
    (assert-true (gbq-identity? f gs '(x y) 'grevlex))
    (assert-true (gbq-identity? f gs '(y x) 'grlex))
    ; в lex (x > y) старший моном x^2 - y — x^2: частное сокращает x^4
    (assert-equal (car (normal-form-with-quotients '(^ x 4) '((- (^ x 2) y)) '(x y) 'lex)) '(^ y 2))))

(deftest "groebner-quot: символы вне переменных — младшие переменные"
  (assert-true (gbq-identity? '(+ (* a (^ x 2)) 1) '((- x 1)) '(x))))
