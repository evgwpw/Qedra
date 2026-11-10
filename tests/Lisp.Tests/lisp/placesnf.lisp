; placesnf.lisp — тесты шага R1-хвост: лог-часть Трагера с местами над ℚ(α) степени ≥ 3 для y² = P (lib/integrate/placesnf.lisp).

(define pnf-P3 '(+ 1 (^ x 3)))
(define pnf-g2 '(+ (^ x 3) -2))
(define pnf-gg2 (integrate::ib-poly-parse pnf-g2 'x))

; кубика g = x³ − x² + 7x − 3 и кривая y² = x³ + 3x + 1: P(α) = (α − 2)², (α, α − 2) — точка порядка 3 над ℚ(α)
(define pnf-g '(+ -3 (* 7 x) (* -1 (^ x 2)) (^ x 3)))
(define pnf-P '(+ 1 (* 3 x) (^ x 3)))
(define pnf-gg (integrate::ib-poly-parse pnf-g 'x))

(define (pnf-int a P)
  (integrate (list '/ a (list '* pnf-g (list '^ P 1/2))) 'x))

(define (pnf-unevaluated? r) (and (pair? r) (equal? (car r) 'integrate)))

; условие risch-nonelementary записано именно для этой формы (условия копятся на весь файл тестов)
(define (pnf-nonelem-cond? e)
  (integrate::int-none-cond? (simplify e) 'x))

; производная ответа против подынтегрального в точках вдали от корней g (root-sum считается численно: вблизи корня шум)
(define (pnf-num-ok? ans e pts)
  (let ((d (integrate::int-diff 'x ans)))
    (every? (lambda (x0)
              (let ((a (eval-num (replace-expr d 'x x0))) (b (eval-num (replace-expr e 'x x0))))
                (< (abs (- a b)) (* 0.000001 (+ 1 (abs b))))))
            pts)))

(deftest "placesnf R1-хвост: ∫dx/((x³−2)√(x³+1)) — доказанный отказ: порядки образа дивизора в J(𝔽_p) различны"
  (let* ((e '(/ 1 (* (+ (^ x 3) -2) (^ (+ (^ x 3) 1) 1/2))))
         (r (integrate e 'x)))
    (assert-true (pnf-unevaluated? r))
    (assert-true (pnf-nonelem-cond? e))
    ; кривая η² = 3(x³+1), места (α, ±3): g = x³ − 2 расщепляется mod 31 и mod 43; порядки E_a − E_b — 7 и 13
    (let ((sc (integrate::nf-scan '(+ 3 (* 3 (^ x 3))) 'x pnf-gg2 (list 3) 'C)))
      (assert-equal 'inconsistent (car sc))
      (assert-true (not (= (nth (nth sc 1) 3) (nth (nth sc 2) 3))))
      (assert-equal '(7 13) (sort (list (nth (nth sc 1) 3) (nth (nth sc 2) 3)) <)))))

(deftest "placesnf R1-хвост: ∫x²/((x³−2)√(x³+1)) элементарен (скручивание c₀ = 3) — ответ проходит int-check"
  (let* ((e '(/ (^ x 2) (* (+ (^ x 3) -2) (^ (+ (^ x 3) 1) 1/2))))
         (r (integrate e 'x)))
    (assert-true (not (pnf-unevaluated? r)))
    (assert-true (int-check r e 'x))))

(deftest "placesnf R1-хвост: ∫x⁵/((x³−2)√(x³+1)) — точная часть на ∞ (2/3)y снята до лог-части"
  (let* ((e '(/ (^ x 5) (* (+ (^ x 3) -2) (^ (+ (^ x 3) 1) 1/2))))
         (r (integrate e 'x)))
    (assert-true (not (pnf-unevaluated? r)))
    (assert-true (int-check r e 'x))))

(deftest "placesnf R1-хвост: ∫x³/((x⁴−2)√(x⁴+1)) — g степени 4, вычет рационален, скручивание"
  (let* ((e '(/ (^ x 3) (* (+ (^ x 4) -2) (^ (+ (^ x 4) 1) 1/2))))
         (r (integrate e 'x)))
    (assert-true (not (pnf-unevaluated? r)))
    (assert-true (int-check r e 'x))))

(deftest "placesnf R1-хвост: прежняя лог-часть — lc < 0 (ряды на ∞ в ℚ(√−1)) больше не даёт ложного «неэлементарен»"
  (let* ((e '(/ (+ (* -1 (^ x 3)) (* -3 (^ x 2)) -4) (* (+ (^ x 3) -2) (^ (+ 3 (* 2 x) (^ x 2) (* -1 (^ x 3))) 1/2))))
         (r (integrate e 'x)))
    (assert-true (not (pnf-unevaluated? r)))
    (assert-true (int-check r e 'x))))

(deftest "placesnf R1-хвост: ряд y(s) — коэффициент при s³ с P‴/3! (раньше P‴/3)"
  (let* ((ys (integrate::dv-y-series pnf-g pnf-P 'x (list -2 1) 4))
         (gg pnf-gg)
         (sq (lambda (r)
               (foldl (lambda (acc i) (integrate::ib-p-add acc (integrate::dv-a-mod (integrate::ib-p-mul (nth ys i) (nth ys (- r i))) gg)))
                      '() (range (+ r 1)))))
         ; коэффициенты P(α + s): 1 + 3α + α³, 3 + 3α², 3α, 1 — mod g
         (pr (list (integrate::dv-a-mod (list 1 3 0 1) gg)
                   (integrate::dv-a-mod (list 3 0 3) gg)
                   (integrate::dv-a-mod (list 0 3) gg)
                   (list 1))))
    (assert-true (every? (lambda (r) (integrate::ib-p-zero? (integrate::dv-a-mod (integrate::ib-p-sub (sq r) (nth pr r)) gg)))
                         '(0 1 2 3)))))

(deftest "placesnf R1-хвост: режим B (Tr ρ ≠ 0) — root-sum по корням g, точная проверка, порядок кручения 3"
  (let* ((a '(+ (^ x 3) (* 4 (^ x 2)) (* -3 x) 2))
         (H (simplify (list '/ (list '* a 'y) (list '* pnf-g pnf-P))))
         (lg (hyp-log-part H pnf-P 'x))
         (sc (integrate::nf-scan pnf-P 'x pnf-gg (list -2 1) 'B))
         (e (list '/ a (list '* pnf-g (list '^ pnf-P 1/2))))
         (r (integrate e 'x)))
    (assert-equal 'logs-sum (car lg))
    (assert-true (nth lg 2))                     ; проверено точно в K[y]/(y² − P(x₀))
    (assert-equal 'order (car sc))
    (assert-equal 3 (nth sc 1))
    (assert-true (not (pnf-unevaluated? r)))
    (assert-true (contains-sym? r 'root-sum))
    (assert-true (pnf-num-ok? r e '(3 5 9/2)))))

(deftest "placesnf R1-хвост: режим B на скрученной кривой y² = 2x³ + 6x + 2 (c₀ = 2)"
  (let* ((P '(+ 2 (* 6 x) (* 2 (^ x 3))))
         (a '(+ (^ x 3) (* 4 (^ x 2)) (* -3 x) 2))
         (e (list '/ a (list '* pnf-g (list '^ P 1/2))))
         (r (integrate e 'x)))
    (assert-true (not (pnf-unevaluated? r)))
    (assert-true (contains-sym? r 'root-sum))
    (assert-true (pnf-num-ok? r e '(3 5 9/2)))))

(deftest "placesnf R1-хвост: режим B, остаток — ненулевой дифференциал 1-го рода ⇒ неэлементарен (q = −1/30)"
  (let* ((e (list '/ 1 (list '* pnf-g (list '^ pnf-P 1/2))))
         (H (simplify (list '/ (list '* 'y) (list '* pnf-g pnf-P))))
         (r (integrate e 'x)))
    (assert-equal 'nonelementary (hyp-log-part H pnf-P 'x))
    (assert-true (pnf-unevaluated? r))
    (assert-true (pnf-nonelem-cond? e))))

(deftest "placesnf R1-хвост: подынтегральные a ∈ ℚ[x]₂ — элементарны ровно (x²+1) и (2x²−x−1) (двумерное ядро)"
  (let* ((tst (lambda (a0 a1 a2)
                (let* ((a (list '+ a0 (list '* a1 'x) (list '* a2 (list '^ 'x 2))))
                       (H (simplify (list '/ (list '* a 'y) (list '* pnf-g pnf-P)))))
                  (hyp-log-part H pnf-P 'x)))))
    (assert-equal 'logs-sum (car (tst 1 0 1)))
    (assert-equal 'logs-sum (car (tst 2 0 2)))
    (assert-equal 'logs-sum (car (tst -1 -1 2)))
    (assert-equal 'nonelementary (tst 1 1 0))
    (assert-equal 'nonelementary (tst 0 1 1))))

(deftest "placesnf R1-хвост: режим C (Tr ρ = 0) с кручением — g = x³+4, y² = x³+1 (точки порядка 3): ответа нет, отказа нет"
  (let* ((e '(/ 1 (* (+ (^ x 3) 4) (^ (+ (^ x 3) 1) 1/2))))
         (r (integrate e 'x))
         (sc (integrate::nf-scan '(+ -3 (* -3 (^ x 3))) 'x (integrate::ib-poly-parse '(+ (^ x 3) 4) 'x) (list 3) 'C)))
    (assert-equal 'order (car sc))
    (assert-equal 3 (nth sc 1))
    (assert-true (every? (lambda (en) (= 3 (nth en 3))) (nth sc 2)))
    (assert-true (pnf-unevaluated? r))
    (assert-true (not (pnf-nonelem-cond? e)))))

(deftest "placesnf R1-хвост: скрученный случай ρ ∈ ℚ с кручением — ∫x²/((x³+4)√(x³+1)): ответ через прежний dv-irred-search"
  (let* ((e '(/ (^ x 2) (* (+ (^ x 3) 4) (^ (+ (^ x 3) 1) 1/2))))
         (r (integrate e 'x)))
    (assert-true (not (pnf-unevaluated? r)))
    (assert-true (int-check r e 'x))))

(deftest "placesnf R1-хвост: подделки — p без корня g, p с одним корнем в режиме C, согласованность меток корней"
  (let* ((Q '(+ 3 (* 3 (^ x 3)))))
    ; x³ ≡ 2 (mod 7) не решается: корней нет
    (assert-equal #f (integrate::nf-prime-data Q 'x pnf-gg2 (list 3) 'B 7))
    ; mod 5 кубы биективны — один корень: режим B годится, режим C (нужны три корня) — нет
    (assert-true (integrate::nf-prime-data Q 'x pnf-gg2 (list 3) 'B 5))
    (assert-equal #f (integrate::nf-prime-data Q 'x pnf-gg2 (list 3) 'C 5))
    ; mod 31 — три корня: 4, 7, 20 (4³ = 64 ≡ 2)
    (let ((pd (integrate::nf-prime-data Q 'x pnf-gg2 (list 3) 'C 31)))
      (assert-equal 3 (length (nth pd 2)))
      (assert-equal '(4 7 20) (sort (map car (nth pd 2)) <)))
    ; циклическая кубика (дисквадрат): g = x³ − 3x + 1, P = 2x³ − 6x + 3, P ≡ 1 (mod g): режим C без доказательства отказа
    (let* ((g '(+ (^ x 3) (* -3 x) 1)) (P '(+ (* 2 (^ x 3)) (* -6 x) 3))
           (H (simplify (list '/ 'y (list '* g P)))))
      (assert-true (galois-disc-square? g 'x))
      (assert-true (not (equal? 'nonelementary (hyp-log-part H P 'x)))))))

(deftest "placesnf R1-хвост: шаги — места над ℚ(α), Кантор по модулю p (α ≡ a), вердикт; английский без русских букв"
  (let* ((e '(/ 1 (* (+ (^ x 3) -2) (^ (+ (^ x 3) 1) 1/2))))
         (cap (capture-step-log (lambda () (integrate e 'x)) 'brief))
         (ru (steps-text (cadr cap) (caddr cap) 'ru))
         (cape (capture-step-log (lambda () (integrate e 'x)) 'brief 'en))
         (en (steps-text (cadr cape) (caddr cape) 'en)))
    (assert-true (string-contains? ru "скручивание η = √c₀·y, c₀ = 3"))
    (assert-true (string-contains? ru "места над ℚ(α), α — корень g = -2 + x^3"))
    (assert-true (string-contains? ru "Кантор по модулю p"))
    (assert-true (string-contains? ru "порядки различны ⇒ дивизор не кручение"))
    (assert-true (string-contains? ru "Неэлементарность доказана"))
    (assert-true (string-contains? en "places over ℚ(α), α is a root of g"))
    (assert-true (string-contains? en "Cantor modulo p"))
    (assert-true (string-contains? en "the orders differ"))
    (assert-true (not (any? (lambda (w) (string-contains? en w)) '("Кантор" "места над" "кручение" "скручивание" "порядки"))))))

(deftest "placesnf R1-хвост: шаги режима B — функция u(t), точная проверка; ru/en"
  (let* ((a '(+ (^ x 3) (* 4 (^ x 2)) (* -3 x) 2))
         (e (list '/ a (list '* pnf-g (list '^ pnf-P 1/2))))
         (cap (capture-step-log (lambda () (integrate e 'x)) 'brief))
         (ru (steps-text (cadr cap) (caddr cap) 'ru))
         (cape (capture-step-log (lambda () (integrate e 'x)) 'brief 'en))
         (en (steps-text (cadr cape) (caddr cape) 'en)))
    (assert-true (string-contains? ru "Tr ρ ≠ 0 — сопряжённые вычеты ℚ-независимы"))
    (assert-true (string-contains? ru "все порядки равны n = 3"))
    (assert-true (string-contains? ru "найдена функция u(t) = (a(x) + b(x)·y)/(x − t)^3"))
    (assert-true (string-contains? en "all orders equal n = 3"))
    (assert-true (string-contains? en "exact check of H"))
    (assert-true (not (any? (lambda (w) (string-contains? en w)) '("Кантор" "найдена" "точная" "сопряжённые"))))))
