; gf.lisp — тесты шага NT.3: конечные поля GF(pⁿ) и многочлены над GF(p) (lib\gf.lisp).
; Каждый сертификат проверяется ещё и «на подделку»: приватные предикаты gf::gf-…-ok? должны отвергать
; испорченное значение (неверный обратный, приводимый «множитель», потерянный множитель, кратность 0, неверный НОД).
; Независимые контрольные значения: AES (FIPS-197, §4.2): {53}⁻¹ = {CA}, {57}·{83} = {C1}; порядок элемента —
; прямым перемножением; число неприводимых монических многочленов степени d над GF(p) — по формуле Гаусса
; N(p,d) = (1/d)·Σ_{e|d} μ(e)·p^(d/e): N(2,1)=2, N(2,2)=1, N(2,3)=2, N(2,4)=3, N(3,1)=3, N(3,2)=3, N(5,1)=5, N(5,2)=10.
; Элементы поля — списки коэффициентов по возрастанию (ноль — ()), многочлены над GF(p) — такие же списки.

; ---------- помощники ----------

; x^(pⁿ) − x над GF(p): 1 при x, −1 при x^(pⁿ)
(define (gft-x-pow-minus-x p n)
  (let ((k (^ p n)))
    (append (list 0 (- p 1)) (map (lambda (i) 0) (range (- k 2))) (list 1))))

; степень многочлена-списка
(define (gft-deg f) (- (length f) 1))

; сколько в fac множителей степени d: fac = (lc ((fᵢ kᵢ) …))
(define (gft-count-deg fac d)
  (length (filter (lambda (fk) (= (gft-deg (car fk)) d)) (cadr fac))))

; число различных элементов списка (по equal?)
(define (gft-distinct l)
  (length (foldl (lambda (acc x) (if (member? x acc) acc (cons x acc))) '() l)))

; ---------- GF(2⁸): поле AES ----------

(deftest "NT.3: GF(2⁸), m = x⁸+x⁴+x³+x+1 (AES): {53}⁻¹ = {CA}"
  (let* ((F (gf-field 2 '(+ 1 x (^ x 3) (^ x 4) (^ x 8)) 'x))
         (F2 (gf-field 2 '(1 1 0 1 1 0 0 0 1) 'x))          ; то же поле, заданное коэффициентами
         (a (gf-elt F 83))                                  ; 0x53 = x⁶+x⁴+x+1
         (ia (gf-inv F a))
         (b (gf-elt F 202)))                                ; 0xCA = x⁷+x⁶+x³+x
    (assert-equal a '(1 1 0 0 1 0 1))
    (assert-equal ia b)
    (assert-equal (gf->int F ia) 202)
    (assert-equal (gf* F a ia) '(1))
    (assert-true (gf::gf-inv-ok? F a ia))
    (assert-equal (gf* F (gf-elt F 83) (gf-elt F 202)) (gf-elt F 1))
    (assert-equal (gf* F '(1 1 0 0 1 0 1) '(1 1 0 0 1 0 1)) (gf* F2 '(1 1 0 0 1 0 1) '(1 1 0 0 1 0 1)))
    (assert-equal (gf->int F (gf* F 87 131)) 193)          ; {57}·{83} = {C1} (FIPS-197)
    (assert-equal (gf/ F 1 83) ia)
    (assert-equal (gf/ F 83 83) (gf-elt F 1))
    (assert-equal (gf/ F 83 3) (gf* F 83 (gf-inv F 3)))
    ; обратные элементы: a·a⁻¹ = 1 для нескольких a
    (assert-true (every? (lambda (x) (equal? (gf* F (gf-elt F x) (gf-inv F x)) (gf-elt F 1)))
                         '(1 2 3 83 87 131 202 255)))
    ; дистрибутивность и аддитивные свойства
    (assert-equal (gf* F (gf+ F 83 3) 5) (gf+ F (gf* F 83 5) (gf* F 3 5)))
    (assert-equal (gf+ F 83 83) (gf-elt F 0))
    (assert-equal (gf- F 83 83) (gf-elt F 0))
    ; элементы и целые
    (assert-equal (gf-elt F 0) '())
    (assert-equal (gf-elt F 256) (gf-elt F 0))             ; 256 = 0 (mod x⁸ …)
    (assert-equal (gf-elt F 1) '(1))
    (assert-equal (gf-elt F '(1 1 0 0 1 0 1 0 1)) '(1 1 0 0 1 0 1))     ; лишние старшие коэффициенты отбрасываются
    ; порядок и первообразность: x имеет порядок 51 (255 = 3·5·17), x+1 — 255
    (assert-equal (gf-order F 2) 51)
    (assert-equal (gf-order F 3) 255)
    (assert-equal (gf-primitive? 2 F) #f)
    (assert-equal (gf-primitive? 3 F) #t)
    (assert-true (gf::gf-order-ok? F 2 51))
    (assert-equal (gf::gf-order-ok? F 2 255) #f)           ; 2⁵¹ = 1 — порядок не 255
    (assert-true (gf::gf-order-ok? F 3 255))
    ; независимая проверка порядка: прямое перемножение
    (assert-equal (let loop ((k 1) (v 3)) (if (equal? v (gf-elt F 1)) k (loop (+ k 1) (gf* F v 3)))) 255)
    (assert-equal (let loop ((k 1) (v 2)) (if (equal? v (gf-elt F 1)) k (loop (+ k 1) (gf* F v 2)))) 51)
    ; степени
    (assert-equal (gf-power F 83 255) (gf-elt F 1))        ; Лагранж: a^(pⁿ−1) = 1
    (assert-equal (gf-power F 83 0) (gf-elt F 1))
    (assert-equal (gf-power F 83 -1) ia)
    (assert-equal (gf-power F 0 0) (gf-elt F 1))
    (assert-equal (gf-power F 87 5)
                  (gf* F (gf* F 87 87) (gf* F 87 (gf* F 87 87))))))

(deftest "NT.3: сертификаты поля отвергают подделку"
  (let ((F (gf-field 2 '(+ 1 x (^ x 3) (^ x 4) (^ x 8)) 'x)))
    ; неверный обратный
    (assert-equal (gf::gf-inv-ok? F 83 203) #f)
    (assert-equal (gf::gf-inv-ok? F 83 202) #t)
    (assert-equal (gf::gf-inv-ok? F 83 '(0)) #f)
    (assert-equal (gf::gf-inv-ok? F 83 '(1 1)) #f)         ; x+1 — не обратный к x⁶+x⁴+x+1
    (assert-equal (gf-inv F 0) #f)
    (assert-equal (gf-inv F '()) #f)
    ; порядок: не минимальный и не делящий pⁿ−1
    (assert-equal (gf::gf-order-ok? F 2 102) #f)           ; 2¹⁰² = 1? 51 | 102, но 102 ∤ … порядок должен делить 255
    (assert-equal (gf::gf-order-ok? F 2 3) #f)
    (assert-equal (gf::gf-order-ok? F 2 1) #f)
    ; вырожденные вызовы
    (assert-error (gf/ F 1 0))
    (assert-error (gf/ F 0 0))
    (assert-error (gf-power F 0 -1))
    (assert-error (gf-power F 2 1/2))
    (assert-error (gf-elt F -1))))

; ---------- GF(3²) ----------

(deftest "NT.3: GF(3²), m = x²+1"
  (let ((F (gf-field 3 '(+ 1 (^ x 2)) 'x))
        (F2 (gf-field 3 '(1 0 1) 'x)))
    (assert-equal (gf+ F '(1 1) '(0 1)) (gf+ F2 '(1 1) '(0 1)))
    (assert-equal (gf* F '(1 1) '(0 1)) (gf* F2 '(1 1) '(0 1)))
    (assert-equal (gf* F '(1 1) '(2 1)) '(1))              ; (1+x)(2+x) = 2+3x+x² = 1
    (assert-equal (gf* F '(0 1) '(0 1)) '(2))              ; x² = −1 = 2
    (assert-equal (gf* F '(0 1) (gf-inv F '(0 1))) '(1))
    (assert-equal (gf-inv F '(0 1)) '(0 2))                ; x⁻¹ = 2x (x·2x = 2x² = 1)
    (assert-equal (gf->int F (gf-inv F '(0 1))) 6)
    (assert-equal (gf- F '(0 1) '(0 2)) '(0 2))            ; x − 2x = −x = 2x
    (assert-equal (gf+ F '(2) '(1)) '())                   ; 2 + 1 = 0
    (assert-equal (gf-elt F 7) '(1 2))                     ; 7 = 1 + 2·3
    (assert-equal (gf->int F '(1 2)) 7)
    (assert-equal (gf-order F '(1 1)) 8)                   ; 1+x — первообразный
    (assert-equal (gf-primitive? '(1 1) F) #t)
    (assert-equal (gf-order F '(0 1)) 4)                   ; x⁴ = 1
    (assert-equal (gf-primitive? '(0 1) F) #f)
    (assert-equal (gf-order F '(2)) 2)                     ; −1
    (assert-error (gf-field 3 '(+ 1 x (^ x 2)) 'x))))      ; x²+x+1 = (x−1)·… — приводим

; ---------- x^(pⁿ) − x = произведение всех неприводимых степеней, делящих n ----------

(deftest "NT.3: x^(pⁿ) − x — произведение всех неприводимых степеней, делящих n"
  (let ((f2 (gf-factor (gft-x-pow-minus-x 2 4) 2)))        ; n = 4: степени 1, 2, 4
    (assert-equal (length (cadr f2)) 6)
    (assert-equal (gft-count-deg f2 1) 2)
    (assert-equal (gft-count-deg f2 2) 1)
    (assert-equal (gft-count-deg f2 4) 3)
    (assert-equal (car f2) 1)
    (assert-true (gf::gf-factor-ok? f2 (gft-x-pow-minus-x 2 4) 2))
    (assert-true (every? (lambda (fk) (gf-irreducible? (car fk) 2)) (cadr f2)))
    (assert-equal (last (car (last (cadr f2)))) 1))        ; последний множитель моничен
  (let ((f3 (gf-factor (gft-x-pow-minus-x 2 3) 2)))        ; n = 3: степени 1 и 3
    (assert-equal (length (cadr f3)) 4)
    (assert-equal (gft-count-deg f3 1) 2)
    (assert-equal (gft-count-deg f3 3) 2)
    (assert-true (gf::gf-factor-ok? f3 (gft-x-pow-minus-x 2 3) 2)))
  (let ((f1 (gf-factor (gft-x-pow-minus-x 2 1) 2)))        ; n = 1: только линейные
    (assert-equal (length (cadr f1)) 2)
    (assert-equal (gft-count-deg f1 1) 2))
  (let ((e3 (gf-factor (gft-x-pow-minus-x 3 2) 3)))        ; n = 2: степени 1 и 2
    (assert-equal (length (cadr e3)) 6)
    (assert-equal (gft-count-deg e3 1) 3)
    (assert-equal (gft-count-deg e3 2) 3)
    (assert-true (gf::gf-factor-ok? e3 (gft-x-pow-minus-x 3 2) 3)))
  (let ((e5 (gf-factor (gft-x-pow-minus-x 5 2) 5)))        ; n = 2: 5 + 10 = 15
    (assert-equal (length (cadr e5)) 15)
    (assert-equal (gft-count-deg e5 1) 5)
    (assert-equal (gft-count-deg e5 2) 10)
    (assert-true (gf::gf-factor-ok? e5 (gft-x-pow-minus-x 5 2) 5))))

; ---------- неприводимость (Рабин) ----------

(deftest "NT.3: gf-irreducible? — критерий Рабина"
  (assert-true (gf-irreducible? '(1 1 0 1 1 0 0 0 1) 2))   ; x⁸+x⁴+x³+x+1 (AES)
  (assert-true (gf-irreducible? '(1 1 1) 2))               ; x²+x+1
  (assert-true (gf-irreducible? '(0 1) 2))                 ; x — степень 1
  (assert-true (gf-irreducible? '(1 1 0 0 1) 2))           ; x⁴+x+1 — примитивный
  (assert-true (gf-irreducible? '(1 1 1 1 1) 2))           ; x⁴+x³+x²+x+1
  (assert-equal (gf-irreducible? '(1 0 1) 2) #f)           ; x²+1 = (x+1)²
  (assert-equal (gf-irreducible? '(1 0 0 1) 2) #f)         ; x³+1 = (x+1)(x²+x+1)
  (assert-equal (gf-irreducible? '(1 0 0 0 1) 2) #f)       ; x⁴+1 = (x+1)⁴
  (assert-true (gf-irreducible? '(2 0 1) 5))               ; x²+2 над GF(5): −2 = 3 — не квадрат
  (assert-equal (gf-irreducible? '(4 0 1) 5) #f)           ; x²+4 = (x−1)(x+1)
  (assert-true (gf-irreducible? '(2 0 2) 3))               ; 2x²+2 = 2(x²+1) — нормируется
  (assert-equal (gf-irreducible? '(1) 3) #f)               ; константа
  (assert-equal (gf-irreducible? '() 3) #f)                ; нуль
  (assert-equal (gf-irreducible? 0 2) #f)
  (assert-error (gf-irreducible? '(1 1 1) 4))              ; p не простое
  (assert-error (gf-irreducible? '(1 1 1) 1)))

; ---------- случайный неприводимый многочлен ----------

(deftest "NT.3: gf-random-irreducible — ответ всегда неприводим"
  (assert-equal (gf-random-irreducible 2 2) '(1 1 1))      ; над GF(2) такой один
  (assert-true (gf-irreducible? (gf-random-irreducible 2 1) 2))
  (let ((rs (map (lambda (i) (gf-random-irreducible 2 4)) (range 8))))
    (assert-true (every? (lambda (f) (and (= (length f) 5) (= (last f) 1) (gf-irreducible? f 2))) rs))
    (assert-true (>= (gft-distinct rs) 2)))
  (let ((qs (map (lambda (i) (gf-random-irreducible 3 2)) (range 12))))
    (assert-true (every? (lambda (f) (and (= (length f) 3) (= (last f) 1) (gf-irreducible? f 3))) qs))
    (assert-equal (gft-distinct qs) 3))                    ; N(3,2) = 3 — все найдены
  (assert-true (gf-irreducible? (gf-random-irreducible 5 3) 5))
  (assert-error (gf-random-irreducible 2 0))
  (assert-error (gf-random-irreducible 4 3))
  (assert-error (gf-random-irreducible 2 1/2)))

; ---------- многочлены над GF(p): НОД ----------

(deftest "NT.3: gf-poly-gcd"
  (assert-equal (gf-poly-gcd '(1 0 0 1) '(1 0 1) 2) '(1 1))    ; x³+1 = (x+1)(x²+x+1), x²+1 = (x+1)²
  (assert-equal (gf-poly-gcd '(2 0 1) '(1 2 1) 3) '(1 1))      ; x²−1 и (x+1)² над GF(3)
  (assert-equal (gf-poly-gcd '(2 0 1) '(1 1) 3) '(1 1))
  (assert-equal (gf-poly-gcd '(1 1 0 0 1) '(1 1 1) 2) '(1))    ; неприводимые различны
  (assert-equal (gf-poly-gcd '(1 0 1) '() 2) '(1 0 1))         ; НОД(f, 0) = моническая часть f
  (assert-equal (gf-poly-gcd '() '() 2) '())
  (assert-equal (gf-poly-gcd '(1 1) '(1 1 1) 2) (gf-poly-gcd '(1 1 1) '(1 1) 2))
  ; сертификат и подделки
  (assert-true (gf::gf-pgcd-ok? 2 '(1 0 0 1) '(1 0 1) '(1 1)))
  (assert-equal (gf::gf-pgcd-ok? 2 '(1 0 0 1) '(1 0 1) '(1)) #f)      ; не настоящий НОД
  (assert-equal (gf::gf-pgcd-ok? 2 '(1 0 0 1) '(1 0 1) '(1 1 1)) #f)  ; r не делит
  (assert-equal (gf::gf-pgcd-ok? 2 '(1 0 1) '() '(1 0 1)) #t)         ; НОД(f, 0) = f
  (assert-equal (gf::gf-pgcd-ok? 2 '(1 1 1) '(1 1) '(1)) #t)          ; взаимно просты — НОД 1
  (assert-error (gf-poly-gcd '(1 1) '(1) 4))
  (assert-error (gf-poly-gcd '(1 1) '(1 1) 0)))

; ---------- разложение: кратности и подделки ----------

(deftest "NT.3: gf-factor — кратности, старший коэффициент, подделки"
  (assert-equal (gf-factor '(1 0 1 1 0 1) 2) '(1 (((1 1) 3) ((1 1 1) 1))))   ; (x+1)³(x²+x+1)
  (assert-equal (gf-factor '(1 0 0 0 1) 2) '(1 (((1 1) 4))))                 ; x⁴+1 = (x+1)⁴
  (assert-equal (gf-factor '(1 0 0 1) 3) '(1 (((1 1) 3))))                   ; x³+1 = (x+1)³ над GF(3)
  (assert-equal (gf-factor '(1 1 1 1 1 1) 3) '(1 (((1 1) 3) ((2 1) 2))))     ; (x+1)³(x+2)²
  (assert-equal (gf-factor '(2 1 2) 3) '(2 (((1 1) 2))))                     ; 2(x+1)²
  (assert-equal (gf-factor '(1 1 1 1) 3) '(1 (((1 1) 1) ((1 0 1) 1))))       ; квадратfree: (x+1)(x²+1)
  (assert-equal (gf-factor 5 3) '(2 ()))                                     ; константа
  (assert-equal (gf-factor '(4) 3) '(1 ()))
  (assert-error (gf-factor '() 2))                                           ; нулевой многочлен
  (assert-error (gf-factor '(4) 2))                                          ; ≡ 0 (mod 2)
  (assert-error (gf-factor '(3) 3))                                          ; ≡ 0 (mod 3)
  (assert-error (gf-factor '(1 0 1) 4))                                      ; p не простое
  ; подделки сертификата: верный ответ принимается,
  (assert-true (gf::gf-factor-ok? '(1 (((1 1) 3) ((1 1 1) 1))) '(1 0 1 1 0 1) 2))
  ; кратность подменена, множитель потерян, произведение не то, множитель приводим,
  (assert-equal (gf::gf-factor-ok? '(1 (((1 1) 2) ((1 1 1) 1))) '(1 0 1 1 0 1) 2) #f)
  (assert-equal (gf::gf-factor-ok? '(1 (((1 1) 3))) '(1 0 1 1 0 1) 2) #f)
  (assert-equal (gf::gf-factor-ok? '(1 (((1 1) 3) ((1 1 1) 1))) 1 2) #f)
  (assert-equal (gf::gf-factor-ok? '(1 (((1 0 1) 1) ((1 1) 1))) '(1 1 1 1) 2) #f)
  ; кратность 0 и немонический множитель (произведение сходится, но множитель не моничен),
  (assert-equal (gf::gf-factor-ok? '(1 (((1 1) 0))) '(1) 2) #f)
  (assert-equal (gf::gf-factor-ok? '(2 (((2 2) 1))) '(2 2) 3) #f)            ; 2x+2 не моничен
  (assert-equal (gf::gf-factor-ok? '(2 (((2 2) 1))) '(1 1) 3) #f)
  (assert-equal (gf::gf-factor-ok? '(1 (((2 2) 1))) '(1 1) 3) #f)
  ; неверный старший коэффициент
  (assert-equal (gf::gf-factor-ok? '(1 (((1 1) 2))) '(2 1 2) 3) #f)
  (assert-true (gf::gf-factor-ok? '(2 (((1 1) 2))) '(2 1 2) 3)))

; ---------- вырожденные случаи поля и ошибки ----------

(deftest "NT.3: gf-field и арифметика — вырожденные случаи"
  (assert-error (gf-field 4 '(+ 1 (^ x 2)) 'x))            ; p не простое
  (assert-error (gf-field 1 '(+ 1 (^ x 2)) 'x))
  (assert-error (gf-field 9 '(+ 1 (^ x 2)) 'x))
  (assert-error (gf-field 2 '(+ 1 (^ x 2)) 'x))            ; x²+1 = (x+1)² — приводим
  (assert-error (gf-field 3 '(+ 1 (* 2 x) (^ x 2)) 'x))    ; (x+1)² — приводим
  (assert-error (gf-field 3 '(+ 2 (* 2 (^ x 2))) 'x))      ; не монический
  (assert-error (gf-field 2 '(0 0) 'x))                    ; нулевой многочлен
  (assert-error (gf-field 2 '(1) 'x))                      ; степень 0
  (assert-error (gf-field 2 '(1 0 1/2) 'x))                ; не целые коэффициенты
  ; GF(2¹) — поле из двух элементов
  (let ((F (gf-field 2 '(0 1) 'x)))
    (assert-equal (gf* F 1 1) '(1))
    (assert-equal (gf-inv F 1) '(1))
    (assert-equal (gf-inv F 0) #f)
    (assert-equal (gf-order F 1) 1)
    (assert-equal (gf-primitive? 1 F) #t)                  ; группа GF(2)* тривиальна
    (assert-equal (gf-primitive? 0 F) #f)
    (assert-error (gf/ F 1 0)))
  ; GF(2⁴): примитивный и непримитивный многочлены
  (let ((Fp (gf-field 2 '(1 1 0 0 1) 'x))
        (Fn (gf-field 2 '(1 1 1 1 1) 'x)))
    (assert-equal (gf-order Fp 2) 15)
    (assert-equal (gf-primitive? 2 Fp) #t)
    (assert-equal (gf-order Fn 2) 5)                       ; x⁵ = 1 в x⁴+x³+x²+x+1
    (assert-equal (gf-primitive? 2 Fn) #f)))
