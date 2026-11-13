; RUBI.MATCH: необязательные аргументы образцов (?a. — Mathematica Optional с Default головы), шаг RUBI.MATCH.
; Семантика: x_ обязательна (сопоставляется только с реально присутствующей частью), x_. при отсутствии части
; получает значение по умолчанию головы: 0 в Plus, 1 в Times, 1 в показателе Power.
; Образцы без точек (написаны вручную, шаг AC.2) работают как раньше: при :identities отсутствие части
; заменяет нейтральный элемент у любой переменной.

; сопоставление «как в движке Rubi»: подготовленный образец + нормализованное выражение (явный режим разметки)
(define (mo-match pat e) (ac-match-prepared (ac-build-prepared pat) (ac-strip-units (ac-norm e)) #f))

(deftest "match-optional: ?a. в сумме получает 0, ?b. в произведении — 1"
  (assert-equal (mo-match '(+ ?a. (* ?b (sin x))) '(* 2 (sin x))) '((?a 0) (?b 2)))
  ; обязательный множитель в ПРОИЗВЕДЕНИИ тоже может выродиться к 1 (Rubi: w_ — «остаток, возможно пустой»)
  (assert-equal (mo-match '(+ ?a. (* ?b (sin x))) '(sin x)) '((?a 0) (?b 1)))
  (assert-equal (mo-match '(+ ?a. (* ?b. (sin x))) '(sin x)) '((?a 0) (?b 1)))
  (assert-equal (mo-match '(+ ?a. (* ?b (sin x))) '(+ 3 (* 2 (sin x)))) '((?a 3) (?b 2)))
  ; НО слагаемое-ноль в сумму не подставляется: a_ (без точки) требует настоящего слагаемого
  (assert-equal (mo-match '(+ ?a (* ?b (sin x))) '(sin x)) #f)
  (assert-equal (mo-match '(* ?a. (cos ?x)) '(cos x)) '((?a 1) (?x x))))

(deftest "match-optional: обязательная переменная не связывается с отсутствующей частью"
  (assert-equal (mo-match '(+ ?a (* ?b (sin x))) '(* 2 (sin x))) #f)
  (assert-equal (mo-match '(+ ?a (* ?b (sin x))) '(sin x)) #f)
  ; в произведении обязательный множитель может выродиться к 1 (см. предыдущий тест), в сумме — нет
  (assert-equal (mo-match '(* ?a (sin x)) '(sin x)) '((?a 1)))
  (assert-equal (mo-match '(+ ?a (* ?b (sin x))) '(+ 3 (* 2 (sin x)))) '((?a 3) (?b 2))))

(deftest "match-optional: показатель степени u^m. — m=1 у не-степени, m обязателен без точки"
  (assert-equal (mo-match '(^ ?u ?n.) 'x) '((?u x) (?n 1)))
  (assert-equal (mo-match '(^ ?u ?n.) '(^ x 2)) '((?u x) (?n 2)))
  (assert-equal (mo-match '(^ ?u. ?n.) '(/ 1 x)) '((?u x) (?n -1)))
  ; как и в произведении, вырождение показателя к 1 разрешено и без точки (иначе правила глав 4–7 теряют ответы)
  (assert-equal (mo-match '(^ ?u ?n) 'x) '((?u x) (?n 1)))
  (assert-equal (mo-match '(^ ?u ?n) '(^ x 2)) '((?u x) (?n 2))))

(deftest "match-optional: линейный аргумент тригонометрии (c_. + d_.*x) при c=0 и d=1"
  ; ∫sin(x)^2 — правило 4.1.1.1 #1: (sin(c_. + d_.*x))^n
  (assert-equal (mo-match '(^ (sin (+ ?c. (* ?d. x))) ?n) '(^ (sin x) 2)) '((?c 0) (?d 1) (?n 2)))
  (assert-equal (mo-match '(^ (sin (+ ?c. (* ?d. x))) ?n) '(^ (sin (+ 1 (* 3 x))) 2)) '((?c 1) (?d 3) (?n 2)))
  ; c_ без точки — сумма в аргументе обязана присутствовать
  (assert-equal (mo-match '(^ (sin (+ ?c (* ?d. x))) ?n) '(^ (sin x) 2)) #f))

(deftest "match-optional: вложенные и оба отсутствующих, повторная переменная"
  (assert-equal (mo-match '(+ ?a. (* ?b. (^ (sin ?x) ?n.))) '(^ (sin y) 2)) '((?a 0) (?b 1) (?x y) (?n 2)))
  (assert-equal (mo-match '(* ?a. ?b. (cos ?x)) '(cos y)) '((?a 1) (?b 1) (?x y)))
  ; та же переменная дважды — согласованность
  (assert-equal (mo-match '(+ ?a. (* ?b. (sin x))) '(* 2 (sin x))) '((?a 0) (?b 2)))
  (assert-equal (mo-match '(+ ?a. (* ?b. (sin ?x)) (* ?c. (sin ?x))) '(+ (* 2 (sin y)) (* 3 (sin z)))) #f))

(deftest "match-optional: сумма из двух обязательных слагаемых требует головы + (образец не вырожден)"
  ; образец правила 1.2.2.2 #35: a_ + b_.*x^2 + c_.*x^4 — обязательна только a
  (let ((p '(+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4)))))
    (assert-equal (mo-match p '(+ (* b (^ x 2)) (* c (^ x 4)))) #f)
    (assert-equal (mo-match p '(+ a (* b (^ x 2)) (* c (^ x 4)))) '((?a a) (?b b) (?c c)))
    ; ?c. без своего слагаемого не даёт c = 1: множитель x^4 обязан присутствовать (1 подставляется только
    ; когда весь множитель — одна необязательная переменная)
    (assert-equal (mo-match p '(+ a (* b (^ x 2)))) #f)
    (assert-equal (mo-match '(* ?a. (cos ?x)) '(cos y)) '((?a 1) (?x y)))))

(deftest "match-optional: инвариант подстановки — ac-subst по привязкам даёт исходное выражение"
  (let ((p '(+ ?a. (* ?b. (^ (sin ?x) ?n.)))))
    (for-each (lambda (e)
                (let ((b (mo-match p e)))
                  (assert-true (pair? b))
                  (assert-equal (simplify (ac-subst p b)) (simplify e))))
              '((^ (sin y) 2) (sin y) (+ 1 (sin y)) (* 3 (^ (sin y) 4)) (+ 2 (* 5 (sin y)))))))

(deftest "match-optional: старые образцы без точек работают как раньше (:identities — любая переменная)"
  (assert-equal (ac-match '(* ?a ?b) 'x :identities #t) '((?a x) (?b 1)))
  (assert-equal (ac-match '(+ ?a ?b) 'x :identities #t) '((?a x) (?b 0)))
  ; без :identities отсутствие аргумента по-прежнему неудача
  (assert-equal (ac-match '(* ?a ?b) 'x) #f)
  ; явный режим (движок Rubi) на образце без разметки: размечать нечего — обязательны все
  (assert-equal (mo-match '(+ ?a (* ?b (sin x))) '(sin x)) #f)
  (assert-equal (mo-match '(+ ?a (* ?b. (sin x))) '(+ 5 (sin x))) '((?a 5) (?b 1))))
