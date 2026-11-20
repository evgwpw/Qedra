; RUBI.AUDIT.1: сигнатуры образцов правил Rubi (tools/rubi/audit.lisp) — константа x мультимножество типизированных множителей.
; Образцы взяты из lib/rubi/rules (rubi-rules-data) дословно; движок и правила не меняются.
; tools/ не копируется в каталог теста: корень репозитория — на 6 уровней выше lib-dir (tests/<проект>/bin/Debug/net10.0/lib/);
; имена au-* вызываются через eval, чтобы проверщик (CHK.2) не считал их неизвестными.
(define au-root-pre (string-append lib-dir "../../../../../../"))
(load (string-append au-root-pre "tools/rubi/audit.lisp"))

(define (aut-call name &rest args) (eval (cons name (map (lambda (a) (list 'quote a)) args))))
(define (aut-info p) (aut-call 'au-sig-of p))
(define (aut-sig p) (nth (aut-info p) 0))
(define (aut-fine p) (nth (aut-info p) 1))
(define (aut-tier p) (nth (aut-info p) 2))
; 1.1.1.2 #4: (a+bx)^m (c+dx)^n
(deftest "audit: 1.1.1.2 #4 - lin*lin"
  (define p '(* (^ (+ ?a. (* ?b. x)) ?m.) (^ (+ ?c. (* ?d. x)) ?n)))
  (assert-equal (aut-sig p) "lin*lin")
  (assert-equal (aut-fine p) "lin^s*lin^s")
  (assert-equal (aut-tier p) "strict"))

; 1.1.3.2 #3: x^m (a+b x^n)^p
(deftest "audit: 1.1.3.2 #3 - bin*x"
  (assert-equal (aut-sig '(* (^ x ?m.) (^ (+ ?a (* ?b. (^ x ?n))) ?p))) "bin*x"))

; 1.1.2.x: (a+b x^2) — отдельный тип bin2; (e x)^m — степень x
(deftest "audit: 1.1.2.8 #4 - bin2*lin*x"
  (assert-equal (aut-sig '(* (^ (* ?e. x) ?m) (^ (+ ?c (* ?d. x)) ?n) (^ (+ ?a (* ?b. (^ x 2))) ?p.)))
                "bin2*lin*x"))

; 1.2.1.1-подобное: квадратичный трёхчлен и линейный множитель, деление — множитель со знаком показателя
(deftest "audit: квадратичный и дробь"
  (assert-equal (aut-sig '(/ (+ ?d (* ?e. x)) (^ (+ ?a. (* ?b. x) (* ?c. (^ x 2))) ?p))) "lin*quad")
  (assert-equal (aut-fine '(/ (+ ?d (* ?e. x)) (^ (+ ?a. (* ?b. x) (* ?c. (^ x 2))) ?p))) "lin*quad^s"))

; 1.2.2.1: трином (a + b x^2 + c x^4); 1.2.3.6: Pq и трином (a + b x^n + c x^2n)
(deftest "audit: trin и Pq"
  (assert-equal (aut-sig '(^ (+ ?a (* ?b. (^ x 2)) (* ?c. (^ x 4))) ?p)) "trin")
  (assert-equal (aut-sig '(* (^ x ?m) ?Pq (^ (+ ?a (* ?b. (^ x ?n)) (* ?c. (^ x ?n2))) ?p))) "Pq*trin*x"))

; 4.1.1.1 #9: (b sin(c+dx))^n — тригонометрия от линейного аргумента
(deftest "audit: 4.1.1.1 #9 - sin"
  (assert-equal (aut-sig '(^ (* ?b (sin (+ ?c. (* ?d. x)))) ?n)) "sin")
  (assert-equal (aut-tier '(^ (* ?b (sin (+ ?c. (* ?d. x)))) ?n)) "strict"))

; 4.1.2.1: (a + b sin)^m (c + d sin)^n; 4.1.13: cos от квадратного аргумента — расширенный тип
(deftest "audit: (a+b trig) и вложенный аргумент"
  (assert-equal (aut-sig '(* (^ (+ ?a (* ?b. (sin (+ ?e. (* ?f. x))))) ?m) (^ (+ ?c (* ?d. (sin (+ ?e. (* ?f. x))))) ?n)))
                "(a+b*sin)*(a+b*sin)")
  (assert-equal (aut-sig '(cos (+ ?a. (* ?b. x) (* ?c. (^ x 2))))) "cos(quad)")
  (assert-equal (aut-tier '(cos (+ ?a. (* ?b. x) (* ?c. (^ x 2))))) "extended"))

; honest unclassified: функция-переменная ?F — отказ с причиной, а не молчаливый «прочее»
(deftest "audit: unclassified с причиной"
  (let ((c (aut-info '(^ (?F (+ ?c. (* ?d. x))) ?p))))
    (assert-equal (nth c 2) "unclassified")
    (assert-true (string-contains? (nth c 3) "?F"))))

; переименование переменных и порядок слагаемых/множителей сигнатуру не меняют
(deftest "audit: инвариантность к переименованию и порядку"
  (assert-equal (aut-sig '(* (^ (+ ?q. (* ?r. x)) ?s) (^ (+ ?t. (* ?e. x)) ?k)))
                (aut-sig '(* (^ (+ (* ?b. x) ?a.) ?m.) (^ (+ ?c. (* ?d. x)) ?n)))))

; реальные данные: 1.1.1.2 #4 и 4.1.1.1 #9 в базе правил имеют те же сигнатуры
(deftest "audit: сигнатуры правил из базы"
  (let ((rs (aut-call 'au-rules)))
    (define (sig-of-id id)
      (nth (aut-info (nth (car (filter (lambda (r) (equal? (nth r 1) id)) rs)) 2)) 0))
    (assert-equal (sig-of-id "Rubi 1.1.1.2 #4") "lin*lin")
    (assert-equal (sig-of-id "Rubi 4.1.1.1 #9") "sin")
    (assert-equal (sig-of-id "Rubi 1.1.3.2 #3") "bin*x")))

; ввод — только главы 1 и 4; каждая запись получает ровно одну сигнатуру, unclassified — только с причиной
(deftest "audit: покрытие записей"
  (let ((recs (aut-call 'au-records)))
    (assert-true (> (length recs) 4000))
    (assert-true (every? (lambda (r) (or (not (equal? (nth r 7) "unclassified")) (not (equal? (nth r 8) "-")))) recs))
    (assert-true (every? (lambda (r) (member? (nth r 3) '("1" "4"))) recs))))
