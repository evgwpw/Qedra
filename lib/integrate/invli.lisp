; invli.lisp — шаг PL.3: ∫x·csc(α+βx) dx и ∫x·sec(α+βx) dx собственными правилами.
; Правил Рича для них нет: 4.5.11 #12 объявляет x^m·csc неберущимся, а ответы корпуса — Li₂ от e^{i·f(x)}.
; Основание: t = tan(v/2), тогда csc v·dv = dt/t и v = 2·atan t, откуда
;   ∫v·csc v dv = i[Li₂(−i t) − Li₂(i t)];   sec — сдвигом v → v + π/2:
;   ∫v·sec v dv = i[Li₂(−i w) − Li₂(i w)] − (π/2)·log w,  w = tan(v/2 + π/4) = (1 + t)/(1 − t).
; Обе формулы проверены численно центральной разностью (совпадение с v·csc v и v·sec v до 1e−10).
(module integrate
  (export int-invli))

; ---------- разбор формы ----------

(define (invli-trig f)                                          ; csc/sec или sin⁻¹/cos⁻¹ → (вид аргумент) | #f
  (cond ((and (pair? f) (equal? (car f) 'csc) (= (length f) 2))   ; (csc u)
         (list 'csc (cadr f)))
        ((and (pair? f) (equal? (car f) 'sec) (= (length f) 2))   ; (sec u)
         (list 'sec (cadr f)))
        ((and (pair? f) (equal? (car f) '^) (= (length f) 3)      ; (^ (sin u) −1)
              (pair? (cadr f)) (member? (car (cadr f)) '(sin cos))
              (equal? (caddr f) -1))
         (list (if (equal? (car (cadr f)) 'sin) 'csc 'sec) (cadr (cadr f))))
        (else #f)))                                             ; не наш случай

(define (invli-term e x)                                        ; c·P(x)·csc(u) → (c P вид u) | #f
  (let* ((sp (ipl-split e x)) (c (car sp)) (vs (cadr sp))         ; постоянный множитель и множители с x
         (tr (filter (lambda (f) (invli-trig f)) vs))             ; тригонометрический множитель
         (rest (filter (lambda (f) (not (invli-trig f))) vs)))     ; остальные
    (and (= (length tr) 1) (= (length rest) 1)                    ; ровно один csc/sec и один многочлен
         (let ((p (car rest)) (t (invli-trig (car tr))))          ; P(x) и (вид аргумент)
           (and t (try (polynomial? p x) (lambda (er) #f))        ; P — многочлен по x
                (<= (length (coefficients p x)) 2)                ; степень не выше первой
                (ipl-lin (cadr t) x)                              ; аргумент линейный
                (list c p (car t) (cadr t)))))))

; ---------- первообразные ----------

(define (invli-half-t v) (list 'tan (list '* 1/2 v)))           ; t = tan(v/2)

(define (invli-csc-prim v)                                      ; ∫v·csc v dv = i[Li₂(−it) − Li₂(it)]
  (let ((t (invli-half-t v)))                                   ; t = tan(v/2)
    (list '* '%i (list '- (list 'polylog 2 (list '* -1 '%i t))   ; i·Li₂(−i t)
                        (list 'polylog 2 (list '* '%i t))))))    ;  − i·Li₂(i t)

(define (invli-sec-w v)                                         ; w = tan(v/2 + π/4) = (1+t)/(1−t)
  (let ((t (invli-half-t v)))                                   ; t = tan(v/2)
    (list '/ (list '+ 1 t) (list '- 1 t))))                      ; отношение

(define (invli-sec-prim v)                                      ; ∫v·sec v dv = i[Li₂(−iw) − Li₂(iw)] − (π/2)·log w
  (let ((w (invli-sec-w v)))                                    ; w = tan(v/2 + π/4)
    (list '- (list '* '%i (list '- (list 'polylog 2 (list '* -1 '%i w)) ; i·Li₂(−i w)
                                 (list 'polylog 2 (list '* '%i w))))    ;  − i·Li₂(i w)
               (list '* (list '/ 'pi 2) (list 'log w)))))       ; −(π/2)·log w

; ---------- ответ ----------

(define (invli-ans e x)                                          ; ответ или #f
  (let ((t (invli-term e x)))                                    ; разбор формы
    (if (not t)
        #f                                                       ; форма не наша
        (let* ((c (car t)) (p (cadr t)) (kind (caddr t)) (u (nth t 3)) ; множитель, P, вид, аргумент
               (cs (coefficients p x))                           ; p0 + p1·x (младшая степень первой)
               (p0 (car cs)) (p1 (if (cdr cs) (cadr cs) 0))       ; коэффициенты P
               (ab (ipl-lin u x)) (al (car ab)) (be (cadr ab))   ; u = α + β·x
               (shift (simplify (list '- p0 (list '* p1 (list '/ al be))))) ; p0 − p1·α/β
               (logv (if (equal? kind 'csc) (invli-half-t u) (invli-sec-w u))) ; tan(u/2) или w
               (prim (if (equal? kind 'csc) (invli-csc-prim u) (invli-sec-prim u))) ; ∫u·csc или ∫u·sec
               (inner (list '+ (list '* shift (list 'log logv))  ; (p0 − p1α/β)·log
                            (list '* (list '/ p1 be) prim))))    ; (p1/β)·∫u·…
          (simplify (list '* c (list '^ be -1) inner))))))       ; c/β и всё вместе

(define (int-invli e x d)                                        ; стратегия каскада
  (invli-ans e x))

(int-add-strategy int-invli)                                     ; регистрация в каскаде
