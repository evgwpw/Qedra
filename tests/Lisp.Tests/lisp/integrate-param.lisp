; Параметры в неопределённых интегралах: разбор случаев по знаку и нулю параметра (lib\integrate\param.lisp).
; Ответ — (piecewise ((условие ответ) ...)); сертификат int-piecewise-check: покрытие всех знаков + проверка ветвей.

(define (pw? r) (and (list? r) (equal? (car r) 'piecewise)))
(define (pw-conds r) (map car (cadr r)))
(define (pw-ans r k) (cadr (nth (cadr r) k)))
(define (ip e) (integrate e 'x))

(deftest "параметры: 1/(x²+a) — три ветви a > 0, a < 0, a = 0"
  (let ((r (ip '(/ 1 (+ (^ x 2) a)))))
    (assert-true (pw? r))
    (assert-equal (pw-conds r) '((> a 0) (< a 0) (= a 0)))
    (assert-equal (pw-ans r 2) '(* -1 (^ x -1)))
    (assert-equal (int-piecewise-check r '(/ 1 (+ (^ x 2) a)) 'x) 'ok)))

(deftest "параметры: 1/(x²+a) — ветви подстановкой: a = 4 даёт atan(x/2)/2, a = −1 даёт логарифм"
  (let ((r (ip '(/ 1 (+ (^ x 2) a)))))
    (assert-true (int-check (subst '(a 4) (pw-ans r 0)) '(/ 1 (+ (^ x 2) 4)) 'x))
    (assert-true (int-check (subst '(a -1) (pw-ans r 1)) '(/ 1 (+ (^ x 2) -1)) 'x))
    (assert-true (contains-sym? (pw-ans r 1) 'log))
    (assert-true (contains-sym? (pw-ans r 0) 'atan))))

(deftest "параметры: декларация a > 0 оставляет одну ветвь и записывает условие"
  (assuming ((a reals positive))
    (let ((r (ip '(/ 1 (+ (^ x 2) a)))))
      (assert-true (not (pw? r)))
      (assert-true (contains-sym? r 'atan))
      (assert-true (int-check r '(/ 1 (+ (^ x 2) a)) 'x)))))

(deftest "параметры: декларация a < 0 — только логарифмическая ветвь"
  (assuming ((a reals negative))
    (let ((r (ip '(/ 1 (+ (^ x 2) a)))))
      (assert-true (not (pw? r)))
      (assert-true (contains-sym? r 'log))
      (assert-true (not (contains-sym? r 'atan)))
      (assert-true (int-check (subst '(a -4) r) '(/ 1 (+ (^ x 2) -4)) 'x)))))

(deftest "параметры: x^a — a ≠ −1 и a = −1"
  (let ((r (ip '(^ x a))))
    (assert-equal (pw-conds r) '((!= a -1) (= a -1)))
    (assert-equal (pw-ans r 1) '(log x))
    (assert-equal (int-piecewise-check r '(^ x a) 'x) 'ok)))

(deftest "параметры: x^a при a ≥ 0 по декларации — один ответ"
  (assuming ((a reals nonnegative))
    (let ((r (ip '(^ x a))))
      (assert-true (not (pw? r)))
      (assert-true (int-check (subst '(a 3) r) '(^ x 3) 'x)))))

(deftest "параметры: exp(a·x) и x·exp(a·x) — a ≠ 0 и a = 0"
  (let ((r1 (ip '(exp (* a x)))) (r2 (ip '(* x (exp (* a x))))))
    (assert-equal (pw-conds r1) '((!= a 0) (= a 0)))
    (assert-equal (pw-ans r1 1) 'x)
    (assert-equal (pw-conds r2) '((!= a 0) (= a 0)))
    (assert-equal (pw-ans r2 1) '(* 1/2 (^ x 2)))
    (assert-equal (int-piecewise-check r1 '(exp (* a x)) 'x) 'ok)
    (assert-equal (int-piecewise-check r2 '(* x (exp (* a x))) 'x) 'ok)))

(deftest "параметры: 1/(a·x+b) — a ≠ 0 и a = 0 (x/b)"
  (let ((r (ip '(/ 1 (+ (* a x) b)))))
    (assert-equal (pw-conds r) '((!= a 0) (= a 0)))
    (assert-equal (pw-ans r 1) '(* (^ b -1) x))
    (assert-equal (int-piecewise-check r '(/ 1 (+ (* a x) b)) 'x) 'ok)))

(deftest "параметры: sin(a·x), cos(a·x) — ветвь a = 0"
  (let ((rs (ip '(sin (* a x)))) (rc (ip '(cos (* a x)))))
    (assert-equal (pw-ans rs 1) 0)
    (assert-equal (pw-ans rc 1) 'x)
    (assert-equal (int-piecewise-check rs '(sin (* a x)) 'x) 'ok)
    (assert-equal (int-piecewise-check rc '(cos (* a x)) 'x) 'ok)))

(deftest "параметры: 1/(x²+bx+c) — по дискриминанту b²−4c"
  (let ((r (ip '(/ 1 (+ (^ x 2) (* b x) c)))))
    (assert-equal (pw-conds r) '((< (+ (^ b 2) (* -4 c)) 0) (> (+ (^ b 2) (* -4 c)) 0) (= (+ (^ b 2) (* -4 c)) 0)))
    (assert-equal (int-piecewise-check r '(/ 1 (+ (^ x 2) (* b x) c)) 'x) 'ok)))

(deftest "параметры: 1/(a²−x²) — a ≠ 0 и a = 0 (a входит в квадрате)"
  (let ((r (ip '(/ 1 (- (^ a 2) (^ x 2))))))
    (assert-equal (pw-conds r) '((!= a 0) (= a 0)))
    (assert-equal (pw-ans r 1) '(^ x -1))
    (assert-equal (int-piecewise-check r '(/ 1 (- (^ a 2) (^ x 2))) 'x) 'ok)))

(deftest "параметры: 1/(x²+a²) — a ≠ 0: atan(x/a)/a, a = 0: −1/x; множитель без x сохраняется"
  (let ((r (ip '(/ 3 (+ (^ x 2) (^ a 2))))))
    (assert-equal (pw-conds r) '((!= a 0) (= a 0)))
    (assert-equal (pw-ans r 1) '(* -3 (^ x -1)))
    (assert-equal (int-piecewise-check r '(/ 3 (+ (^ x 2) (^ a 2))) 'x) 'ok)))

(deftest "сертификат piecewise: подделка — atan при a < 0 отвергается"
  (let ((e '(/ 1 (+ (^ x 2) a)))
        (bad (list 'piecewise (list (list '(> a 0) '(* (^ a -1/2) (atan (* (^ a -1/2) x))))
                                    (list '(< a 0) '(* (^ a -1/2) (atan (* (^ a -1/2) x))))
                                    (list '(= a 0) '(* -1 (^ x -1)))))))
    (let ((v (int-piecewise-check bad e 'x)))
      (assert-equal (car v) 'bad)
      (assert-true (string-contains? (cadr v) "(< a 0)")))))

(deftest "сертификат piecewise: подделка — нет ветви a = 0, покрытие нарушено"
  (let* ((r (ip '(/ 1 (+ (^ x 2) a))))
         (cut (list 'piecewise (list (car (cadr r)) (cadr (cadr r))))))
    (let ((v (int-piecewise-check cut '(/ 1 (+ (^ x 2) a)) 'x)))
      (assert-equal (car v) 'bad)
      (assert-true (string-contains? (cadr v) "не покрывают")))))

(deftest "сертификат piecewise: подделка — неверная формула в ветви a ≠ −1"
  (let ((bad '(piecewise (((!= a -1) (^ x (+ a 1))) ((= a -1) (log x))))))
    (assert-equal (car (int-piecewise-check bad '(^ x a) 'x)) 'bad)))

(deftest "сертификат piecewise: ветвь a = 0 у exp(a·x) подменена — отвергается"
  (let ((bad '(piecewise (((!= a 0) (* (^ a -1) (exp (* a x)))) ((= a 0) 0)))))
    (assert-equal (car (int-piecewise-check bad '(exp (* a x)) 'x)) 'bad)))

(deftest "параметры: без символьных параметров и вне семейств — прежний ответ (не piecewise)"
  (assert-true (not (pw? (ip '(/ 1 (+ (^ x 2) 4))))))
  (assert-true (not (pw? (ip '(* a x)))))
  (assert-true (not (pw? (ip '(* a (sin x))))))
  (assert-true (not (pw? (ip '(+ (^ x 2) (* a x))))))
  (assert-true (not (pw? (ip '(exp (* 2 x)))))))

(deftest "piecewise: diff по ветвям (раньше 0), d/dx ∫x^a = x^a по ветвям"
  (assert-equal '(piecewise (((> a 0) (* 2 x)) ((<= a 0) 1))) (diff 'x '(piecewise (((> a 0) (^ x 2)) ((<= a 0) x)))))
  (assert-equal '(piecewise (((!= a -1) (^ x a)) ((= a -1) (^ x -1)))) (diff 'x (integrate '(^ x a) 'x))))
