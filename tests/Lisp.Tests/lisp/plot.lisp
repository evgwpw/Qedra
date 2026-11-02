; plot.lisp — тесты шага P1: двумерные графики в SVG (адаптивная сетка, разрывы, асимптоты).

(define (tpl-near? a b tol) (< (abs (- a b)) tol))
(define (tpl-pts segs) (append-map (lambda (s) s) segs))
(define (tpl-segs spec) (plot::pl-get (plot::pl-analyze-spec spec '()) :segments))
(define (tpl-max l) (foldl (lambda (m v) (if (> v m) v m)) (car l) l))
(define (tpl-min l) (foldl (lambda (m v) (if (< v m) v m)) (car l) l))
(define (tpl-opt info key)
  (cond ((null? info) '())
        ((equal? (car info) key) (cadr info))
        (else (tpl-opt (cddr info) key))))
(define (tpl-count-sub s sub)
  (let loop ((i 0) (n 0))
    (cond ((> (+ i (string-length sub)) (string-length s)) n)
          ((equal? (substring s i (+ i (string-length sub))) sub) (loop (+ i 1) (+ n 1)))
          (else (loop (+ i 1) n)))))

(deftest "plot: x^2 на [-2,2] — одна ломаная, yrange ≈ [0,4]"
  (let ((i (plot-info '(^ x 2) 'x -2 2)))
    (assert-equal (tpl-opt i :segments) 1)
    (assert-equal (tpl-opt i :asymptotes) '())
    (assert-true (tpl-near? (car (tpl-opt i :yrange)) 0 0.01))
    (assert-true (tpl-near? (cadr (tpl-opt i :yrange)) 4 0.01))))

(deftest "plot: 1/x на [-1,1] — две ломаные, асимптота 0, через 0 не соединено"
  (let ((i (plot-info '(^ x -1) 'x -1 1))
        (segs (plot-sample '(^ x -1) 'x -1 1 '())))
    (assert-equal (tpl-opt i :segments) 2)
    (assert-equal (length (tpl-opt i :asymptotes)) 1)
    (assert-true (tpl-near? (car (tpl-opt i :asymptotes)) 0 1e-6))
    (assert-equal (length segs) 2)
    (assert-true (every? (lambda (s) (or (every? (lambda (p) (< (car p) 0)) s)
                                         (every? (lambda (p) (> (car p) 0)) s)))
                         segs))))

(deftest "plot: fake — plot-info 1/x не отдаёт ломаную через 0 (в записи вида (/ 1 x) тоже)"
  (let ((segs (plot-sample '(/ 1 x) 'x -2 2 '())))
    (assert-equal (length segs) 2)
    (assert-true (not (any? (lambda (s) (and (any? (lambda (p) (< (car p) 0)) s) (any? (lambda (p) (> (car p) 0)) s))) segs)))
    (assert-equal (tpl-opt (plot-info '(/ 1 x) 'x -2 2) :holes) '())))

(deftest "plot: tan x на [-4,4] — асимптоты ±π/2, ≥ 3 ломаных, ±3π/2 вне отрезка"
  (let* ((i (plot-info '(tan x) 'x -4 4)) (as (tpl-opt i :asymptotes)))
    (assert-equal (length as) 2)
    (assert-true (tpl-near? (car as) (- (/ 3.141592653589793 2)) 1e-6))
    (assert-true (tpl-near? (cadr as) (/ 3.141592653589793 2) 1e-6))
    (assert-true (>= (tpl-opt i :segments) 3))))

(deftest "plot: tan x на [-5,5] — четыре асимптоты (±π/2, ±3π/2)"
  (assert-equal (length (tpl-opt (plot-info '(tan x) 'x -5 5) :asymptotes)) 4))

(deftest "plot: sin x / x — дыра в 0, не асимптота"
  (let ((i (plot-info '(/ (sin x) x) 'x -3 3)))
    (assert-equal (tpl-opt i :asymptotes) '())
    (assert-equal (length (tpl-opt i :holes)) 1)
    (assert-true (tpl-near? (car (tpl-opt i :holes)) 0 1e-6))
    (assert-true (tpl-near? (cadr (tpl-opt i :yrange)) 1 1e-3))))

(deftest "plot: 1/(x^2-1) — асимптоты ±1 и три ломаные"
  (let* ((i (plot-info '(/ 1 (- (^ x 2) 1)) 'x -3 3)) (as (tpl-opt i :asymptotes)))
    (assert-equal (length as) 2)
    (assert-true (tpl-near? (car as) -1 1e-6))
    (assert-true (tpl-near? (cadr as) 1 1e-6))
    (assert-equal (tpl-opt i :segments) 3)))

(deftest "plot: log x на [-1,2] — для x ≤ 0 не определён, асимптота 0"
  (let* ((i (plot-info '(log x) 'x -1 2)) (pts (tpl-pts (plot-sample '(log x) 'x -1 2 '()))))
    (assert-equal (tpl-opt i :segments) 1)
    (assert-equal (length (tpl-opt i :asymptotes)) 1)
    (assert-true (tpl-near? (car (tpl-opt i :asymptotes)) 0 1e-6))
    (assert-true (every? (lambda (p) (> (car p) 0)) pts))))

(deftest "plot: sqrt(1-x^2) на [-2,2] — область [-1,1], края достигнуты"
  (let ((pts (tpl-pts (plot-sample '(sqrt (- 1 (^ x 2))) 'x -2 2 '()))))
    (assert-true (every? (lambda (p) (and (>= (car p) -1) (<= (car p) 1))) pts))
    (assert-true (any? (lambda (p) (> (car p) 0.999)) pts))
    (assert-true (any? (lambda (p) (< (car p) -0.999)) pts))
    (assert-true (every? (lambda (p) (and (>= (cadr p) 0) (<= (cadr p) 1.0001))) pts))))

(deftest "plot: параметрическая окружность — замкнута, x,y ∈ [-1,1]"
  (let* ((i (plot-info '(:parametric (cos t) (sin t) t 0 (* 2 pi))))
         (segs (tpl-pts (tpl-segs '(:parametric (cos t) (sin t) t 0 (* 2 pi)))))
         (f (car segs)) (l (last segs)))
    (assert-equal (tpl-opt i :segments) 1)
    (assert-true (tpl-near? (car f) (car l) 1e-9))
    (assert-true (tpl-near? (cadr f) (cadr l) 1e-9))
    (assert-true (every? (lambda (p) (and (<= (abs (car p)) 1.0000001) (<= (abs (cadr p)) 1.0000001))) segs))
    (assert-true (tpl-near? (cadr (tpl-opt i :yrange)) 1 1e-3))))

(deftest "plot: полярная кардиоида r = 1 + cos θ"
  (let* ((spec '(:polar (+ 1 (cos th)) th 0 (* 2 pi)))
         (pts (tpl-pts (tpl-segs spec))))
    (assert-equal (tpl-opt (plot-info spec) :segments) 1)
    (assert-true (tpl-near? (tpl-max (map car pts)) 2 1e-3))
    (assert-true (tpl-near? (tpl-min (map car pts)) (- 0.25) 1e-2))
    (assert-true (tpl-near? (tpl-max (map cadr pts)) 1.299 1e-2))))

(deftest "plot: SVG — структура и экранирование заголовка и подписей"
  (let* ((s (plot-svg (list '((^ x 2) x -2 2 :label "a<b & c")) (list :legend #t :title "T<1 & \"q\"")))
         (n 1))
    (assert-equal (substring s 0 4) "<svg")
    (assert-true (string-contains? s "viewBox=\"0 0 600 400\""))
    (assert-true (string-contains? s "T&lt;1 &amp; &quot;q&quot;"))
    (assert-true (string-contains? s "a&lt;b &amp; c"))
    (assert-true (not (string-contains? s "a<b")))
    (assert-equal (tpl-count-sub s "<path") 1)
    (assert-equal (tpl-count-sub s "</svg>") 1)
    (assert-equal (tpl-count-sub s "<svg") 1)
    (assert-equal (tpl-count-sub s "<text") (tpl-count-sub s "</text>"))
    (assert-equal n 1)))

(deftest "plot: SVG — несколько кривых: цвета, легенда, асимптоты пунктиром"
  (let ((s (plot-svg (list '((^ x -1) x -2 2) '((sin x) x -2 2 :color "#abcdef")) '())))
    (assert-equal (tpl-count-sub s "<path") 3)
    (assert-true (string-contains? s "stroke-dasharray"))
    (assert-true (string-contains? s "#1f77b4"))
    (assert-true (string-contains? s "#abcdef"))
    (assert-true (string-contains? s "y = sin(x)"))
    (assert-true (string-contains? s "y = 1/x"))))

(deftest "plot: plot — удобная обёртка, опции размеров"
  (let ((s (plot '(sin x) 'x 0 '(* 2 pi) :width 300 :height 200)))
    (assert-true (string-contains? s "viewBox=\"0 0 300 200\""))
    (assert-equal (tpl-count-sub s "<path") 1)))

(deftest "plot: красивые метки 1, 2, 5 × 10^k"
  (assert-equal (map cdr (plot::pl-ticks 0 10)) '("0" "2" "4" "6" "8" "10"))
  (assert-equal (map cdr (plot::pl-ticks 0 1)) '("0" "0.2" "0.4" "0.6" "0.8" "1"))
  (assert-equal (map cdr (plot::pl-ticks -1 1)) '("-1" "-0.5" "0" "0.5" "1"))
  (assert-equal (map cdr (plot::pl-ticks 0 500)) '("0" "100" "200" "300" "400" "500")))

(deftest "plot: адаптивная выборка сгущается у 0 для sin(1/x) на [0.01, 1]"
  (let ((pts (tpl-pts (plot-sample '(sin (/ 1 x)) 'x 0.01 1 '()))))
    (assert-true (> (length (filter (lambda (p) (< (car p) 0.1)) pts))
                    (* 3 (length (filter (lambda (p) (> (car p) 0.9)) pts)))))))

(deftest "plot: :ymin/:ymax — обрезка на границе, а не отбрасывание"
  (let* ((segs (plot-sample '(^ x -1) 'x -1 1 '(:ymin -5 :ymax 5))) (pts (tpl-pts segs)))
    (assert-equal (length segs) 2)
    (assert-true (every? (lambda (p) (<= (abs (cadr p)) 5.0000001)) pts))
    (assert-true (any? (lambda (p) (tpl-near? (cadr p) 5 1e-9)) pts))
    (assert-true (any? (lambda (p) (tpl-near? (cadr p) -5 1e-9)) pts))))

(deftest "plot: скачок x/|x| — две ломаные, это скачок, не асимптота"
  (let ((i (plot-info '(/ x (abs x)) 'x -3 3)))
    (assert-equal (tpl-opt i :segments) 2)
    (assert-equal (tpl-opt i :asymptotes) '())
    (assert-equal (length (tpl-opt i :jumps)) 1)))

(deftest "plot: ошибки — a ≥ b и неверная спецификация"
  (assert-error (plot-info '(^ x 2) 'x 2 -2))
  (assert-error (plot-svg (list '(^ x 2)) '())))

(deftest "plot: всё не определено — пустой график, SVG валиден"
  (let ((s (plot '(sqrt (- -1 (^ x 2))) 'x -1 1)))
    (assert-equal (tpl-count-sub s "<path") 0)
    (assert-equal (substring s 0 4) "<svg")))

;; ---------- шаг P1b: равный масштаб, дыры, односторонние полюса, неявные кривые ----------
(define (tpl-spec-info spec opts) (plot::pl-analyze-spec spec opts))
(define (tpl-isegs spec opts) (plot::pl-get (tpl-spec-info spec opts) :segments))
;; пикселей на единицу по x и по y
(define (tpl-scales specs opts)
  (let ((fr (plot::pl-frame-of specs opts)))
    (list (/ (nth fr 6) (- (nth fr 9) (nth fr 8))) (/ (nth fr 7) (- (nth fr 11) (nth fr 10))))))
(define (tpl-ends segs) (append-map (lambda (s) (list (car s) (last s))) segs))
(define (tpl-dist0 p) (+ (abs (car p)) (abs (cadr p))))
(define tpl-circ '(:implicit (- (+ (^ x 2) (^ y 2)) 1) x y -2 2 -2 2))

(deftest "plot P1b: равный масштаб — параметрическая окружность и кардиоида, :auto отключает"
  (let ((sc (tpl-scales (list '(:parametric (cos t) (sin t) t 0 (* 2 pi))) '()))
        (sp (tpl-scales (list '(:polar (+ 1 (cos th)) th 0 (* 2 pi))) '()))
        (sa (tpl-scales (list '(:parametric (cos t) (sin t) t 0 (* 2 pi))) '(:aspect :auto)))
        (sf (tpl-scales (list '((sin x) x 0 6)) '()))
        (se (tpl-scales (list '((sin x) x 0 6)) '(:aspect :equal))))
    (assert-true (tpl-near? (car sc) (cadr sc) 1e-9))
    (assert-true (tpl-near? (car sp) (cadr sp) 1e-9))
    (assert-true (> (abs (- (car sa) (cadr sa))) 10))
    (assert-true (> (abs (- (car sf) (cadr sf))) 10))
    (assert-true (tpl-near? (car se) (cadr se) 1e-9))))

(deftest "plot P1b: дыра sin x / x рисуется пустым кружком в (0, 1)"
  (let* ((specs (list '((/ (sin x) x) x -10 10)))
         (fr (plot::pl-frame-of specs '()))
         (px (+ (nth fr 2) (* (nth fr 6) (/ (- 0 (nth fr 8)) (- (nth fr 9) (nth fr 8))))))
         (py (+ (nth fr 4) (* (nth fr 7) (/ (- (nth fr 11) 1) (- (nth fr 11) (nth fr 10))))))
         (s (plot-svg specs '())))
    (assert-true (string-contains? s (string-append "<circle cx=\"" (plot::pl-f2 px) "\" cy=\"" (plot::pl-f2 py) "\" r=\"3\" fill=\"#ffffff\"")))
    (assert-equal (tpl-count-sub s "data-kind=\"hole\"") 1)))

(deftest "plot P1b: exp(1/x) — односторонний полюс в 0, диапазон по y не раздут"
  (let* ((i (plot-info '(exp (^ x -1)) 'x -1 1)) (yr (tpl-opt i :yrange)) (os (tpl-opt i :one-sided)))
    (assert-equal (length (tpl-opt i :asymptotes)) 1)
    (assert-true (tpl-near? (car (tpl-opt i :asymptotes)) 0 1e-6))
    (assert-equal (tpl-opt i :segments) 2)
    (assert-equal (length os) 1)
    (assert-true (tpl-near? (car (car os)) 0 1e-6))
    (assert-equal (cadr (car os)) 'right)
    (assert-true (<= (cadr yr) 50))
    (assert-true (>= (car yr) -1e-9))))

(deftest "plot P1b: log x — односторонняя асимптота справа; 1/x — двусторонняя, :one-sided пуст"
  (assert-equal (cadr (car (tpl-opt (plot-info '(log x) 'x -1 2) :one-sided))) 'right)
  (assert-equal (tpl-opt (plot-info '(^ x -1) 'x -1 1) :one-sided) '()))

(deftest "plot P1b: неявная окружность x²+y²=1 — замкнута, на кривой, равный масштаб"
  (let* ((segs (tpl-isegs tpl-circ '(:n 80))) (pts (tpl-pts segs)))
    (assert-equal (length segs) 1)
    (assert-true (tpl-near? (car (car pts)) (car (last pts)) 1e-12))
    (assert-true (tpl-near? (cadr (car pts)) (cadr (last pts)) 1e-12))
    (assert-true (every? (lambda (p) (< (abs (- (+ (* (car p) (car p)) (* (cadr p) (cadr p))) 1)) 1e-3)) pts))
    (assert-true (> (length pts) 80))
    (let ((sc (tpl-scales (list tpl-circ) '(:n 80))))
      (assert-true (tpl-near? (car sc) (cadr sc) 1e-9)))))

(deftest "plot P1b: фолиум Декарта — узел (0,0) отмечен, ветви сходятся в нём"
  (let* ((spec '(:implicit (- (+ (^ x 3) (^ y 3)) (* 3 x y)) x y -2 2 -2 2))
         (r (tpl-spec-info spec '(:n 80)))
         (segs (plot::pl-get r :segments)) (sing (plot::pl-get r :singular)))
    (assert-equal (length sing) 1)
    (assert-true (< (tpl-dist0 (car sing)) 1e-9))
    (assert-true (>= (length (filter (lambda (p) (< (tpl-dist0 p) 0.05)) (tpl-ends segs))) 4))
    (assert-true (every? (lambda (p) (< (abs (- (+ (^ (car p) 3) (^ (cadr p) 3)) (* 3 (car p) (cadr p)))) 0.05)) (tpl-pts segs)))
    (assert-true (> (length segs) 1))
    (assert-true (string-contains? (plot-svg (list spec) '(:n 40)) "data-kind=\"singular\""))))

(deftest "plot P1b: лемниската (x²+y²)² = x²−y² — узел в начале координат"
  (let* ((spec '(:implicit (- (^ (+ (^ x 2) (^ y 2)) 2) (- (^ x 2) (^ y 2))) x y -1.5 1.5 -1 1))
         (r (tpl-spec-info spec '(:n 60)))
         (segs (plot::pl-get r :segments)) (pts (tpl-pts segs)))
    (assert-equal (length (plot::pl-get r :singular)) 1)
    (assert-true (>= (length (filter (lambda (p) (< (tpl-dist0 p) 0.05)) (tpl-ends segs))) 2))
    (assert-true (tpl-near? (tpl-max (map car pts)) 1 0.03))
    (assert-true (tpl-near? (tpl-min (map car pts)) -1 0.03))))

(deftest "plot P1b: полукубическая парабола y² = x³ — точка возврата отмечена"
  (let* ((spec '(:implicit (- (^ y 2) (^ x 3)) x y -2 2 -2 2))
         (r (tpl-spec-info spec '(:n 80)))
         (segs (plot::pl-get r :segments)))
    (assert-equal (length (plot::pl-get r :singular)) 1)
    (assert-true (< (tpl-dist0 (car (plot::pl-get r :singular))) 1e-9))
    (assert-true (any? (lambda (p) (< (tpl-dist0 p) 0.02)) (tpl-pts segs)))
    (assert-true (every? (lambda (p) (> (car p) -0.001)) (tpl-pts segs)))))

(deftest "plot P1b: гипербола x²−y²=1 — две компоненты, x = 0 не пересекают"
  (let ((segs (tpl-isegs '(:implicit (- (^ x 2) (^ y 2) 1) x y -3 3 -3 3) '(:n 60))))
    (assert-equal (length segs) 2)
    (assert-true (every? (lambda (s) (or (every? (lambda (p) (> (car p) 0)) s) (every? (lambda (p) (< (car p) 0)) s))) segs))
    (assert-true (any? (lambda (s) (> (car (car s)) 0)) segs))
    (assert-true (any? (lambda (s) (< (car (car s)) 0)) segs))))

(deftest "plot P1b: пустая кривая x²+y²+1=0 — без звеньев и ошибок, SVG валиден"
  (let* ((spec '(:implicit (+ (^ x 2) (^ y 2) 1) x y -2 2 -2 2))
         (i (plot-info spec))
         (s (plot-svg (list spec) '(:n 40))))
    (assert-equal (tpl-opt i :segments) 0)
    (assert-equal (tpl-opt i :singular) '())
    (assert-equal (tpl-count-sub s "<path") 0)
    (assert-equal (substring s 0 4) "<svg")))

(deftest "plot P1b: plot-implicit, форма (= l r), не многочлен, ошибка окна"
  (let ((s (plot-implicit '(= (^ x 2) (- 1 (^ y 2))) 'x 'y -2 2 -2 2 :n 40 :title "T")))
    (assert-equal (tpl-count-sub s "<path") 1)
    (assert-true (string-contains? s ">T</text>")))
  (let ((r (tpl-spec-info '(:implicit (- (sin x) (cos y)) x y -3 3 -3 3) '(:n 40))))
    (assert-true (> (length (plot::pl-get r :segments)) 0))
    (assert-equal (plot::pl-get r :singular) '()))
  (assert-error (plot-implicit '(- x y) 'x 'y 2 -2 -1 1))
  (assert-equal (plot::pl-opt (plot-info '(:implicit (- x y) x y -1 1 -1 1)) :segments 0) 1))

;; ---------- Шаг P1d: честный график и линии уровня ----------
(define (tpl-in-any? ivs v) (any? (lambda (u) (and (<= (car u) v) (<= v (cadr u)))) ivs))

(deftest "plot P1d: sin x на [0,10] — сертификат полный, без неопределённых ячеек"
  (let ((i (plot-info '(sin x) 'x 0 10 '(:certified #t :columns 16))))
    (assert-equal (tpl-opt i :certified) #t)
    (assert-equal (tpl-opt i :uncertain) '())
    (assert-true (<= (cadr (tpl-opt i :enclosure)) 1.0001))
    (assert-true (>= (car (tpl-opt i :enclosure)) -1.0001))
    (assert-true (>= (cadr (tpl-opt i :enclosure)) 0.99))))

(deftest "plot P1d: узкий пик 1/(x²+1e-6) — оболочка видит пик, грубая выборка нет"
  (let ((f '(/ 1 (+ (^ x 2) 0.000001)))
        (plain (plot-info '(/ 1 (+ (^ x 2) 0.000001)) 'x -1 1.1 '(:n 7)))
        (cert (plot-info '(/ 1 (+ (^ x 2) 0.000001)) 'x -1 1.1 '(:n 7 :certified #t))))
    (assert-true (< (cadr (tpl-opt plain :yrange)) 100000))
    (assert-true (>= (cadr (tpl-opt cert :enclosure)) 100000))
    (assert-equal (tpl-opt cert :certified) #f)
    (assert-true (tpl-in-any? (tpl-opt cert :uncertain) 0.0))))

(deftest "plot P1d: 1/x на [-1,1] — неопределённость только у полюса"
  (let* ((i (plot-info '(/ 1 x) 'x -1 1 '(:certified #t :columns 12)))
         (u (tpl-opt i :uncertain))
         (cells (plot::pl-opt (plot-certificate '(/ 1 x) 'x -1 1 :columns 12) :cells '())))
    (assert-equal (tpl-opt i :certified) #f)
    (assert-equal (length u) 1)
    (assert-true (tpl-in-any? u 0.0))
    (assert-true (< (- (cadr (car u)) (car (car u))) 0.2))
    (assert-true (every? (lambda (c) (if (or (<= (nth c 1) -1/5) (>= (nth c 0) 1/5)) (equal? (nth c 2) 'ok) #t)) cells))))

(deftest "plot P1d: функция вне интервальной арифметики — неопределённо, не сертифицировано"
  (let ((i (plot-info '(abs x) 'x -1 1 '(:certified #t :columns 4 :depth 1))))
    (assert-equal (tpl-opt i :certified) #f)
    (assert-true (tpl-in-any? (tpl-opt i :uncertain) 0.5))
    (assert-true (tpl-in-any? (tpl-opt i :uncertain) -0.5)))
  (let ((i (plot-info '(tan x) 'x -1 1 '(:certified #t :columns 6))))
    (assert-equal (tpl-opt i :certified) #t)))

(deftest "plot P1d: подделка сертификата — проверка не проходит"
  (let* ((cert (plot-certificate '(sin x) 'x 0 4 :columns 6))
         (cells (plot::pl-opt cert :cells '()))
         (c0 (car cells))
         (rep (lambda (cs) (list :tol (plot::pl-opt cert :tol 0) :cells cs))))
    (assert-true (plot-certificate-check '(sin x) 'x 0 4 cert))
    ;; сузили верхний конец первой ячейки до нижнего
    (assert-true (not (plot-certificate-check '(sin x) 'x 0 4
                        (rep (cons (list (nth c0 0) (nth c0 1) 'ok (nth c0 3) (nth c0 3)) (cdr cells))))))
    ;; выбросили ячейку — щель
    (assert-true (not (plot-certificate-check '(sin x) 'x 0 4 (rep (cdr (cdr cells))))))
    ;; другая функция
    (assert-true (not (plot-certificate-check '(cos x) 'x 0 4 cert))))
  (let* ((cert (plot-certificate '(/ 1 x) 'x -1 1 :columns 4 :depth 2))
         (cells (plot::pl-opt cert :cells '()))
         (bad (filter (lambda (c) (member? (nth c 2) '(fail wide))) cells))
         (fake (map (lambda (c) (if (member? (nth c 2) '(fail wide)) (list (nth c 0) (nth c 1) 'ok -1 1) c)) cells)))
    (assert-true (pair? bad))
    (assert-true (plot-certificate-check '(/ 1 x) 'x -1 1 cert))
    (assert-true (not (plot-certificate-check '(/ 1 x) 'x -1 1 (list :tol 100 :cells fake))))))

(deftest "plot P1d: SVG честного графика — полосы включений и неопределённые полосы"
  (let ((s (plot '(/ 1 x) 'x -1 1 :certified #t :columns 8 :depth 3))
        (p (plot '(/ 1 x) 'x -1 1)))
    (assert-true (> (tpl-count-sub s "data-kind=\"enclosure\"") 0))
    (assert-true (> (tpl-count-sub s "data-kind=\"uncertain\"") 0))
    (assert-equal (tpl-count-sub p "data-kind=\"uncertain\"") 0)
    (assert-equal (substring s 0 4) "<svg")))

(deftest "plot P1d: линии уровня x²+y² — окружности, число уровней, нет линий вне диапазона"
  (let* ((r (plot::pl-ct-analyze '(+ (^ x 2) (^ y 2)) 'x 'y -2 2 -2 2 '(:n 40)))
         (cs (plot::pl-get r :contours)))
    (assert-true (and (>= (length cs) 7) (<= (length cs) 11)))
    (assert-true (every? (lambda (c) (pair? (cadr c))) cs))
    (assert-true (every? (lambda (c)
                           (every? (lambda (p) (tpl-near? (+ (* (car p) (car p)) (* (cadr p) (cadr p))) (car c) 0.06))
                                   (tpl-pts (cadr c))))
                         cs)))
  (let* ((r (plot::pl-ct-analyze '(+ (^ x 2) (^ y 2)) 'x 'y -2 2 -2 2 '(:n 40 :levels (-1 1 9))))
         (cs (plot::pl-get r :contours)))
    (assert-equal (map (lambda (c) (length (cadr c))) cs) '(0 1 0))))

(deftest "plot P1d: седло x²−y², уровень 0 — две пересекающиеся прямые"
  (let* ((r (plot::pl-ct-analyze '(- (^ x 2) (^ y 2)) 'x 'y -2 2 -2 2 '(:n 40 :levels (0))))
         (pts (tpl-pts (cadr (car (plot::pl-get r :contours))))))
    (assert-true (any? (lambda (p) (and (> (abs (car p)) 1) (tpl-near? (car p) (cadr p) 0.03))) pts))
    (assert-true (any? (lambda (p) (and (> (abs (car p)) 1) (tpl-near? (car p) (- (cadr p)) 0.03))) pts))
    (assert-true (every? (lambda (p) (tpl-near? (abs (car p)) (abs (cadr p)) 0.03)) pts))))

(deftest "plot P1d: sin x · cos y и plot-contour — SVG, легенда, plot-info по уровням"
  (let ((i (plot-info '(:contour (* (sin x) (cos y)) x y -3 3 -3 3) '(:n 30)))
        (s (plot-contour '(* (sin x) (cos y)) 'x 'y -3 3 -3 3 :n 30)))
    (assert-true (> (length (tpl-opt i :levels)) 5))
    (assert-equal (length (tpl-opt i :polylines)) (length (tpl-opt i :levels)))
    (assert-true (> (apply + (map cadr (tpl-opt i :polylines))) 0))
    (assert-equal (tpl-count-sub s "data-level=") (apply + (map cadr (tpl-opt i :polylines))))
    (assert-true (string-contains? s "data-kind=\"legend\""))
    (assert-equal (substring s 0 4) "<svg")))

; ---- Шаг P2: трёхмерные поверхности ----
(define (tp3-depths s)
  (map (lambda (part) (string->number (substring part 0 (string-index part "\""))))
       (cdr (string-split s "data-depth=\""))))
(define (tp3-sorted-desc? l)
  (or (null? l) (null? (cdr l)) (and (>= (car l) (cadr l)) (tp3-sorted-desc? (cdr l)))))
(define (tp3-balanced? s)
  (and (equal? (substring s 0 4) "<svg")
       (string-contains? s "viewBox=")
       (= (tpl-count-sub s "<svg") 1) (= (tpl-count-sub s "</svg>") 1)
       (= (tpl-count-sub s "<g ") (tpl-count-sub s "</g>"))
       (= (tpl-count-sub s "<text") (tpl-count-sub s "</text>"))))
(define tp3-paraboloid '(+ (^ x 2) (^ y 2)))

(deftest "plot3d: параболоид x²+y² — квадов n², zrange [0, 2], без обрезки"
  (let ((i (plot3d-info tp3-paraboloid 'x 'y -1 1 -1 1 :n 20)))
    (assert-equal (tpl-opt i :quads) 400)
    (assert-equal (tpl-opt i :holes) 0)
    (assert-equal (tpl-opt i :clipped) #f)
    (assert-true (tpl-near? (car (tpl-opt i :zrange)) 0 1e-9))
    (assert-true (tpl-near? (cadr (tpl-opt i :zrange)) 2 1e-9))))

(deftest "plot3d: седло x²−y² — zrange [−1, 1] на [−1, 1]²"
  (let ((i (plot3d-info '(- (^ x 2) (^ y 2)) 'x 'y -1 1 -1 1 :n 20)))
    (assert-equal (tpl-opt i :quads) 400)
    (assert-true (tpl-near? (car (tpl-opt i :zrange)) -1 1e-9))
    (assert-true (tpl-near? (cadr (tpl-opt i :zrange)) 1 1e-9))))

(deftest "plot3d: рябь sin(√(x²+y²)) — ограничена [−1, 1], не обрезается"
  (let ((i (plot3d-info '(sin (sqrt (+ (^ x 2) (^ y 2)))) 'x 'y -6 6 -6 6 :n 24)))
    (assert-equal (tpl-opt i :quads) 576)
    (assert-equal (tpl-opt i :clipped) #f)
    (assert-true (<= (cadr (tpl-opt i :zrange)) 1.0000001))
    (assert-true (>= (car (tpl-opt i :zrange)) -1.0000001))
    (assert-true (> (cadr (tpl-opt i :zrange)) 0.9))))

(deftest "plot3d: 1/(x²+y²) у нуля — полюс обрезан, zrange ограничен; :zmax переопределяет"
  (let ((i (plot3d-info '(/ 1 (+ (^ x 2) (^ y 2))) 'x 'y -1 1 -1 1 :n 24))
        (j (plot3d-info '(/ 1 (+ (^ x 2) (^ y 2))) 'x 'y -1 1 -1 1 :n 24 :zmax 3)))
    (assert-equal (tpl-opt i :clipped) #t)
    (assert-true (< (cadr (tpl-opt i :zrange)) 50))
    (assert-true (>= (car (tpl-opt i :zrange)) 0.5))
    (assert-true (> (tpl-opt i :holes) 0))
    (assert-equal (tpl-opt j :clipped) #t)
    (assert-true (tpl-near? (cadr (tpl-opt j :zrange)) 3 1e-9))))

(deftest "plot3d: √(1−x²−y²) на [−1, 1]² — дыры вне круга"
  (let ((i (plot3d-info '(sqrt (- 1 (+ (^ x 2) (^ y 2)))) 'x 'y -1 1 -1 1 :n 20)))
    (assert-equal (+ (tpl-opt i :quads) (tpl-opt i :holes)) 400)
    (assert-true (> (tpl-opt i :holes) 80))
    (assert-true (> (tpl-opt i :quads) 200))
    (assert-equal (tpl-opt i :clipped) #f)
    (assert-true (tpl-near? (cadr (tpl-opt i :zrange)) 1 1e-9))
    ;; квады в SVG — ровно недырявые
    (let ((s (plot3d '(sqrt (- 1 (+ (^ x 2) (^ y 2)))) 'x 'y -1 1 -1 1 :n 20)))
      (assert-equal (tpl-count-sub s "<polygon") (tpl-opt i :quads)))))

(deftest "plot3d: параметрическая сфера — все вершины на единичной сфере"
  (let* ((spec '(:parametric-surface (* (cos u) (sin v)) (* (sin u) (sin v)) (cos v) u 0 (* 2 pi) v 0 pi))
         (rows (plot3d-points spec :n 12))
         (pts (append-map (lambda (r) r) rows)))
    (assert-equal (length pts) 169)
    (assert-true (every? (lambda (p) (and p (tpl-near? (+ (^ (car p) 2) (^ (cadr p) 2) (^ (caddr p) 2)) 1 1e-9))) pts))
    (assert-equal (tpl-opt (plot3d-info spec :n 12) :quads) 144)
    (assert-true (tp3-balanced? (plot3d-svg (list spec) '(:n 12))))))

(deftest "plot3d: тор — вершины на торе, квады n²"
  (let* ((spec '(:parametric-surface (* (+ 2 (cos v)) (cos u)) (* (+ 2 (cos v)) (sin u)) (sin v) u 0 (* 2 pi) v 0 (* 2 pi)))
         (pts (append-map (lambda (r) r) (plot3d-points spec :n 10))))
    (assert-true (every? (lambda (p)
                         (tpl-near? (+ (^ (- (sqrt (+ (^ (car p) 2) (^ (cadr p) 2))) 2) 2) (^ (caddr p) 2)) 1 1e-9))
                       pts))
    (assert-equal (tpl-opt (plot3d-info spec :n 10) :quads) 100)
    (assert-true (tpl-near? (car (tpl-opt (plot3d-info spec :n 10) :zrange)) -1 0.1))))

(deftest "plot3d: алгоритм художника — data-depth не возрастает"
  (let* ((s (plot3d '(* (sin x) (cos y)) 'x 'y -3 3 -3 3 :n 14))
         (d (tp3-depths s)))
    (assert-equal (length d) 196)
    (assert-true (tp3-sorted-desc? d))
    (assert-true (> (car d) (tpl-min d)))
    (let ((s2 (plot3d tp3-paraboloid 'x 'y -1 1 -1 1 :n 14 :azimuth 200 :elevation 60 :perspective 6)))
      (assert-true (tp3-sorted-desc? (tp3-depths s2))))))

(deftest "plot3d: поворот — азимут 0 и 90 дают разные проекции, одинаковое число квадов"
  (let* ((f '(+ (^ x 2) (* 2 x y)))
         (a (plot3d f 'x 'y -1 1 -1 1 :n 10 :azimuth 0))
         (b (plot3d f 'x 'y -1 1 -1 1 :n 10 :azimuth 90)))
    (assert-true (not (equal? a b)))
    (assert-equal (tpl-count-sub a "<polygon") (tpl-count-sub b "<polygon"))
    (assert-equal (tpl-count-sub a "<polygon") 100)
    (assert-equal (plot3d-info f 'x 'y -1 1 -1 1 :n 10 :azimuth 0) (plot3d-info f 'x 'y -1 1 -1 1 :n 10 :azimuth 90))
    (assert-equal a (plot3d f 'x 'y -1 1 -1 1 :n 10 :azimuth 0))))

(deftest "plot3d: корректный SVG — оси, подписи, экранирование, сетка, линии уровня на полу"
  (let* ((s (plot3d tp3-paraboloid 'x 'y -1 1 -1 1 :n 10 :mesh #t :floor-contours #t :title "a<b & c"))
         (m (plot3d tp3-paraboloid 'x 'y -1 1 -1 1 :n 10)))
    (assert-true (tp3-balanced? s))
    (assert-true (tp3-balanced? m))
    (assert-true (string-contains? s "a&lt;b &amp; c"))
    (assert-true (string-contains? s "floor-contour"))
    (assert-true (not (string-contains? m "floor-contour")))
    (assert-true (string-contains? s ">z</text>"))
    (assert-true (string-contains? s ">x</text>"))
    (assert-true (string-contains? s "#333333"))
    (assert-true (not (string-contains? s "http://www.w3.org/1999/xlink")))
    (assert-true (not (string-contains? s "href")))))

(deftest "plot3d: несколько поверхностей и ошибки"
  (let ((s (plot3d-svg (list '(:surface (+ (^ x 2) (^ y 2)) x y -1 1 -1 1)
                             '(:surface (- 3 (^ x 2)) x y -1 1 -1 1))
                       '(:n 8))))
    (assert-equal (tpl-count-sub s "<polygon") 128)
    (assert-true (tp3-sorted-desc? (tp3-depths s))))
  (assert-true (try (begin (plot3d-svg '((:surface x x y 1 0 -1 1)) '()) #f) (lambda (e) #t)))
  (assert-true (try (begin (plot3d tp3-paraboloid 'x 'y -1 1 -1 1 :perspective 1) #f) (lambda (e) #t)))
  (assert-true (try (begin (plot3d-svg '((:foo 1)) '()) #f) (lambda (e) #t))))
