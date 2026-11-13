; RUBI.C11: `Times`/`Plus` в Mathematica — Flat (одна переменная образца берёт несколько аргументов).
; Без этого правила «P(x)*(квадратичный двучлен)^p» не срабатывают, и файл 1.1.2.9 отвечает своим последним
; правилом Unintegrable (задача 1.2.1.3/1341 из loss-12). Тест охраняет: (1) групповую привязку ?Px,
; (2) отсутствие лишних групповых решений у `(* ?w ?u ?v)` (главы 4–7 не должны замедляться),
; (3) саму задачу 1.2.1.3/1341.
(load (string-append lib-dir "rubi/utils.lisp"))

; другие файлы тестов подменяют правила Rubi игрушечными наборами — возвращаем настоящие
(define (rfl-fresh)
  (set! rubi::*rubi-rules* '())
  (set! rubi::*rubi-ord* 0)
  (set! rubi::*rubi-loaded* #f)
  (set! rubi::*rubi-stage* 0)
  (set! rubi::*rubi-bodies* (make-hash))
  (set! rubi::*rubi-bodies-loaded* (make-hash)))

(define (rfl-prep pat e)
  (ac-match-prepared (ac-build-prepared pat) (ac-strip-units (ac-norm e)) #f))

(deftest "rubi-flat/1: ?Px берёт группу множителей (Px_ против (A + B x)*(d + e x)*(a + c x^2)^p)"
  ; образец правила 1.1.2.9 «P(x)*(a + c x^2)^p»: многочлен здесь — произведение двух линейных
  (assert-equal (rfl-prep '(* ?Px (^ (+ ?a (* ?c (^ x 2))) ?p))
                          '(* (+ A (* B x)) (+ d (* e1 x)) (^ (+ a (* c (^ x 2))) -2)))
                '((?Px (* (+ A (* B x)) (+ d (* e1 x)))) (?a a) (?c c) (?p -2)))
  ; одиночная привязка по-прежнему первая: без развёрнутого произведения ?Px — один множитель
  (assert-equal (rfl-prep '(* ?Px ?u) '(* (+ A (* B x)) (sin x)))
                '((?Px (+ A (* B x))) (?u (sin x)))))

(deftest "rubi-flat/2: `(* ?w ?u ?v)` не даёт группового решения для первой переменной"
  (let ((b (rfl-prep '(* ?w ?u ?v) '(* a b c))))
    (assert-true (pair? b))
    (assert-true (not (and (pair? (cadr (assoc '?w b))) (equal? (car (cadr (assoc '?w b))) '*))))
    (assert-equal (cadr (assoc '?w b)) 'a)))

(deftest "rubi-flat/3: 1.2.1.3/1341 (A + B x)*(d + e x)/(a + c x^2)^2 — ответ есть и верен численно"
  (rfl-fresh)
  (let* ((e (math-read "(A + B*x)*(d + e1*x)/(a + c*x^2)^2"))
         (r (rubi-integrate e 'x)))
    (assert-true (not (equal? r 'unknown)))
    (assert-true (not (contains-sym? r 'integrate)))
    ; x > 0 и x < 0: подынтегральное рационально, точек достаточно
    (assert-equal 'ok (integrate::int-numeric-status-at (list '- (integrate::int-diff 'x r) e) r 'x 0.000001 '(-1.7 -0.4 0.6 1.9)))))
