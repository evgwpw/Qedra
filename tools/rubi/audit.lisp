; tools/rubi/audit.lisp — RUBI.AUDIT.1: сигнатуры образцов правил Rubi глав 1 и 4 и дерево «сигнатура -> правила».
;
; Офлайн-анализ, движок не затрагивается. Читаются те же S-выражения правил, что исполняет движок (rubi::*rubi-rules*,
; образец — (nth r 2), порядок Rubi — (nth r 0)). Как tools/rubi/taxonomy.lisp: Lisp печатает таблицы в stdout,
; файлы пишет обёртка tools/rubi/audit.mjs (язык не пишет файлы).
;   node tools/rubi/audit.mjs                       ; research/rubi/audit/{signatures.tsv,tree-1.txt,tree-4.txt,coverage.tsv,selfcheck.tsv}
;   Lisp.exe tools/rubi/audit.lisp -e "(au-sig-of '(* (^ (+ ?a (* ?b. x)) ?m.) (+ ?c (* ?d. x))))"
;
; Сигнатура образца = мультимножество типизированных множителей (константы — множители без x и без произвольных
; переменных ?u ?Pq — отбрасываются), отсортированное и соединённое через «*»; пустое — «K».
; Типы множителя (грубая сигнатура — без показателей):
;   x       — степень x (x, c*x в степени)            lin   — (a + b x)
;   quad    — (a + b x + c x^2) и (b x + c x^2)        bin2  — (a + b x^2)
;   bin     — (a + b x^n), n не 1 и не 2               trin  — (a + b x^n + c x^n2), также x^2 и x^n
;   bin-gen — (a x^p + b x^q) без константы            trin-gen — три члена x^k без константы
;   Pq      — многочлен-переменная ?Pq ?Qx ?Rn …       u    — произвольная переменная ?u ?v ?w ?y ?z ?Fx
;   sin cos tan cot sec csc — тригонометрия от линейного аргумента; sinh … csch, log — так же
;   sin(<сиг>) — тригонометрия/log от НЕлинейного аргумента (в скобках — сигнатура аргумента)
;   (a+b*sin), (a+b*sin^e) — (a + b trig(lin)) и (a + b trig(lin)^показатель)
;   sum[…]  — прочая сумма: типы членов через «,» («1» — член без x)
; Показатели в точной сигнатуре (sig_exp): ^s — символьный, ^i — целый литерал ≠ 1, ^f — дробный литерал.
; unclassified — узел, не лёгший ни в один тип (причина — в таблице): функция-переменная ?F, неизвестная голова, …
;
; Уровни: strict — только типы карточки (x lin quad bin bin2 trin Pq тригонометрия от линейного a+b*trig);
; extended — плюс u, hyp, log, вложенные аргументы, прочие суммы; unclassified — не классифицировано.

; ---------- загрузка правил ----------
; au-root-pre (необязательно) — корень репозитория с «/» на конце: тест грузит файл не из корня (см. tests/Lisp.Tests/lisp/rubi-audit.lisp)
(load (string-append (if (bound? 'au-root-pre) (eval 'au-root-pre) "") "tools/rubi/taxonomy.lisp"))

(define (au-rules)
  (rubi::rubi-ensure)
  (rubi::rubi-ensure-full)
  (filter (lambda (r)
            (and (string? (nth r 9))
                 (> (string-length (nth r 9)) 1)
                 (let ((c (substring (nth r 9) 0 2))) (or (equal? c "1.") (equal? c "4.")))))
          rubi::*rubi-rules*))

; ---------- малые утилиты ----------
(define (au-fail msg) (raise (list 'au-unclass msg)))

(define (au-sym-name s) (symbol->string s))

; ?a. -> "a", ?Pq -> "Pq"
(define (au-vname v)
  (let* ((s (au-sym-name v)) (s1 (substring s 1 (string-length s))))
    (if (and (> (string-length s1) 0) (equal? (substring s1 (- (string-length s1) 1) (string-length s1)) "."))
        (substring s1 0 (- (string-length s1) 1))
        s1)))

(define (au-pvar? e)
  (and (symbol? e) (> (string-length (au-sym-name e)) 1) (equal? (substring (au-sym-name e) 0 1) "?")))

(define (au-poly-var? e)
  (and (au-pvar? e) (member? (substring (au-vname e) 0 1) '("P" "Q" "R"))))

(define (au-arb-var? e)
  (and (au-pvar? e)
       (or (au-poly-var? e) (member? (au-vname e) '("u" "v" "w" "y" "z" "Fx")))))

; без x и без произвольных переменных (?u может зависеть от x)
(define (au-free? e)
  (cond ((equal? e 'x) #f)
        ((symbol? e) (not (au-arb-var? e)))
        ((pair? e) (every? au-free? e))
        (else #t)))

(define (au-join l sep)
  (cond ((null? l) "")
        ((null? (cdr l)) (car l))
        (else (string-append (car l) sep (au-join (cdr l) sep)))))

(define (au-sorted l) (sort l string<?))

; ---------- показатели ----------
; число | рациональный литерал (/ n d) -> число; иначе 's (символьный)
(define (au-exp e)
  (cond ((number? e) e)
        ((and (pair? e) (equal? (car e) '/) (= (length e) 3) (number? (cadr e)) (number? (caddr e))
              (not (= (caddr e) 0)))
         (/ (cadr e) (caddr e)))
        ((and (pair? e) (equal? (car e) '-) (= (length e) 2) (number? (cadr e))) (- 0 (cadr e)))
        (else 's)))

(define (au-exp-mul a b) (if (or (equal? a 's) (equal? b 's)) 's (* a b)))
(define (au-exp-neg a) (if (equal? a 's) 's (- 0 a)))

; множители: ((основание . показатель) ...); * и / раскрываются, (^ B E) — показатель перемножается
(define (au-factors e ex)
  (cond ((and (pair? e) (equal? (car e) '*))
         (append-map (lambda (t) (au-factors t ex)) (cdr e)))
        ((and (pair? e) (equal? (car e) '/) (= (length e) 3))
         (append (au-factors (cadr e) ex) (au-factors (caddr e) (au-exp-neg ex))))
        ((and (pair? e) (equal? (car e) '^) (= (length e) 3))
         (au-factors (cadr e) (au-exp-mul ex (au-exp (caddr e)))))
        (else (list (cons e ex)))))

(define (au-terms e)
  (if (and (pair? e) (equal? (car e) '+)) (cdr e) (list e)))

; тег показателя для точной сигнатуры
(define (au-exp-tag ex)
  (cond ((equal? ex 's) "^s")
        ((= ex 1) "")
        ((integer? ex) "^i")
        (else "^f")))

; ---------- типы ----------
(define au-trig-heads '(sin cos tan cot sec csc))
(define au-fun-heads '(sin cos tan cot sec csc sinh cosh tanh coth sech csch log))

; (грубый-тип . члены) множителя без показателя: строка или raise
(define (au-base-type b)
  (cond ((equal? b 'x) "x")
        ((au-free? b) "K")
        ((au-poly-var? b) "Pq")
        ((au-arb-var? b) "u")
        ((au-pvar? b) "K")
        ((symbol? b) (au-fail (string-append "символ " (au-sym-name b))))
        ((not (pair? b)) "K")
        ((equal? (car b) '+) (au-sum-type b))
        ((and (symbol? (car b)) (member? (car b) au-fun-heads) (= (length b) 2))
         (let ((as (au-expr-sig (cadr b))))
           (if (or (equal? as "x") (equal? as "lin"))
               (au-sym-name (car b))
               (string-append (au-sym-name (car b)) "(" as ")"))))
        ((and (symbol? (car b)) (au-pvar? (car b)))
         (au-fail (string-append "функция-переменная " (au-sym-name (car b)))))
        ((symbol? (car b)) (au-fail (string-append "голова " (au-sym-name (car b)))))
        (else (au-fail "составная голова"))))

; тип члена суммы со степенью x и показателями: «1», «x», «x^2», «x^n», «sin^n», «sin*x» …
(define (au-term-type t)
  (let* ((fs (au-factors t 1))
         (parts (filter (lambda (s) (not (equal? s "")))
                        (map (lambda (f)
                               (let ((ty (au-base-type (car f))) (ex (cdr f)))
                                 (cond ((equal? ty "K") "")
                                       ((equal? ty "x")
                                        (cond ((equal? ex 's) "x^n") ((= ex 1) "x") ((= ex 2) "x^2") (else "x^n")))
                                       ((equal? ex 's) (string-append ty "^e"))
                                       ((= ex 1) ty)
                                       (else (string-append ty "^e")))))
                             fs))))
    (if (null? parts) "1" (au-join (au-sorted parts) "*"))))

(define (au-trig-term? ty)
  (let ((h (car (string-split ty "^"))))
    (member? h '("sin" "cos" "tan" "cot" "sec" "csc"))))

; au-relaxed: самопроверка сравнивает ещё и «со склейкой» bin2 -> bin (подстановка n = 2 вместо ?n)
(define au-relaxed #f)

(define (au-sum-type e)
  (let* ((tt (au-sorted (map au-term-type (au-terms e))))
         (has1 (member? "1" tt))
         (nz (filter (lambda (s) (not (equal? s "1"))) tt)))
    (cond ((equal? nz '("x")) "lin")
          ((equal? nz '("x" "x^2")) "quad")
          ((and has1 (equal? nz '("x^2"))) (if au-relaxed "bin" "bin2"))
          ((and has1 (equal? nz '("x^n"))) "bin")
          ((and (every? (lambda (s) (or (equal? s "x^n") (equal? s "x^2"))) nz) (= (length nz) 2))
           (if has1 "trin" "bin-gen"))
          ((and (not has1) (every? (lambda (s) (or (equal? s "x^n") (equal? s "x^2"))) nz) (= (length nz) 3))
           "trin-gen")
          ((and has1 (= (length nz) 1) (au-trig-term? (car nz)))
           (string-append "(a+b*" (car nz) ")"))
          (else (string-append "sum[" (au-join tt ",") "]")))))

; точный и грубый типы множителей выражения: ((грубый . точный) ...), без констант
(define (au-factor-types e)
  (filter (lambda (p) (not (equal? (car p) "K")))
          (map (lambda (f)
                 (let ((ty (au-base-type (car f))))
                   (cons ty (string-append ty (if (equal? ty "K") "" (au-exp-tag (cdr f)))))))
               (au-factors e 1))))

(define (au-sig-string ps which)           ; which: car — грубая, cdr — точная
  (if (null? ps)
      "K"
      (au-join (au-sorted (map (lambda (p) (if (equal? which 'coarse) (car p) (cdr p))) ps)) "*")))

(define (au-expr-sig e)
  (au-sig-string (au-factor-types e) 'coarse))

; ---------- уровень ----------
(define au-strict-types '("x" "lin" "quad" "bin" "bin2" "trin" "Pq" "sin" "cos" "tan" "cot" "sec" "csc"))

(define (au-strict-type? ty)
  (or (member? ty au-strict-types)
      (and (> (string-length ty) 4) (equal? (substring ty 0 4) "(a+b"))))

; (sig sig-exp tier reason): tier = strict | extended | unclassified
(define (au-classify e)
  (try
   (let* ((ps (au-factor-types e))
          (coarse (au-sig-string ps 'coarse))
          (fine (au-sig-string ps 'fine))
          (strict (every? (lambda (p) (au-strict-type? (car p))) ps)))
     (list coarse fine (if strict "strict" "extended") "-"))
   (lambda (err)
     (let ((d (error-data err)))
       (if (and (pair? d) (equal? (car d) 'au-unclass))
           (list "unclassified" "unclassified" "unclassified" (cadr d))
           (list "unclassified" "unclassified" "unclassified"
                 (string-append "внутренняя ошибка: " (to-string (error-message err)))))))))

(define (au-sig-of e) (au-classify e))

; ---------- разделы ----------
; файл правил -> раздел: гл. 1 — три номера (1.1.1), гл. 4 — два (4.1); «1.3.3-2» -> 1.3.3
(define (au-file-base f)
  (let ((i (string-index f "-"))) (if i (substring f 0 i) f)))

(define (au-section f)
  (let* ((parts (string-split (au-file-base f) "."))
         (n (if (equal? (car parts) "1") 3 2)))
    (au-join (au-take parts n) ".")))

(define (au-take l n) (if (or (null? l) (= n 0)) '() (cons (car l) (au-take (cdr l) (- n 1)))))

(define (au-chapter f) (substring f 0 1))

; номер правила: «Rubi 1.1.1.2 #4» -> "4"
(define (au-num r)
  (let ((i (string-index (nth r 1) "#"))) (substring (nth r 1) (+ i 1) (string-length (nth r 1)))))

(define (au-short r) (string-append (nth r 9) "#" (au-num r)))

; ---------- таблицы ----------
(define au-cache #f)

; записи: (id file ord chapter section sig fine tier reason family)
(define (au-records)
  (if au-cache
      au-cache
      (begin
        (set! au-cache
              (map (lambda (r)
                     (let* ((c (au-classify (nth r 2)))
                            (fam (try (symbol->string (car (eval (list 'rubi-rule-family (list 'quote r))))) (lambda (e) "?"))))
                       (list (nth r 1) (nth r 9) (nth r 0) (au-chapter (nth r 9)) (au-section (nth r 9))
                             (nth c 0) (nth c 1) (nth c 2) (nth c 3) fam)))
                   (sort (au-rules) (lambda (a b) (< (nth a 0) (nth b 0))))))
        au-cache)))

(define (au-f rec i) (nth rec i))

(define (au-tsv-line l) (display (au-join (map to-string l) "\t")) (newline))

(define (au-print-signatures)
  (display "id\tfile\tord\tsection\tsignature\tsignature_exp\ttier\tfamily\treason")
  (newline)
  (for-each (lambda (r)
              (au-tsv-line (list (au-f r 0) (au-f r 1) (au-f r 2) (au-f r 4) (au-f r 5) (au-f r 6) (au-f r 7)
                                 (au-f r 9) (au-f r 8))))
            (au-records)))

(define (au-uniq l)
  (let loop ((l l) (acc '()))
    (cond ((null? l) (reverse acc))
          ((member? (car l) acc) (loop (cdr l) acc))
          (else (loop (cdr l) (cons (car l) acc))))))

(define (au-pct n d)
  (if (= d 0)
      "-"
      (let ((pm (floor (+ 0.5 (* 1000.0 (/ n (* 1.0 d)))))))
        (string-append (number->string (quotient pm 10)) "." (number->string (modulo pm 10))))))

(define (au-count pred l) (length (filter pred l)))

(define (au-cov-row label rs)
  (let* ((n (length rs))
         (st (au-count (lambda (r) (equal? (au-f r 7) "strict")) rs))
         (ex (au-count (lambda (r) (equal? (au-f r 7) "extended")) rs))
         (un (au-count (lambda (r) (equal? (au-f r 7) "unclassified")) rs))
         (leaves (length (au-uniq (map (lambda (r) (au-f r 5)) rs)))))
    (au-tsv-line (list label n st ex un (au-pct (+ st ex) n) (au-pct st n) leaves))))

(define (au-print-coverage)
  (display "scope\trules\tstrict\textended\tunclassified\tclassified_pct\tstrict_pct\tleaves")
  (newline)
  (let ((recs (au-records)))
    (for-each (lambda (ch) (au-cov-row (string-append "chapter " ch) (filter (lambda (r) (equal? (au-f r 3) ch)) recs)))
              '("1" "4"))
    (for-each (lambda (s) (au-cov-row s (filter (lambda (r) (equal? (au-f r 4) s)) recs)))
              (au-uniq (map (lambda (r) (au-f r 4)) recs)))))

; причины unclassified: «причина<TAB>число<TAB>пример id»
(define (au-print-reasons)
  (display "reason\trules\texample")
  (newline)
  (let* ((recs (filter (lambda (r) (equal? (au-f r 7) "unclassified")) (au-records)))
         (rs (au-uniq (map (lambda (r) (au-f r 8)) recs))))
    (for-each
     (lambda (re)
       (let ((sel (filter (lambda (r) (equal? (au-f r 8) re)) recs)))
         (au-tsv-line (list re (length sel) (au-f (car sel) 0)))))
     (sort rs (lambda (a b) (> (au-count (lambda (r) (equal? (au-f r 8) a)) recs)
                               (au-count (lambda (r) (equal? (au-f r 8) b)) recs)))))))

; ---------- дерево ----------
; лист = грубая сигнатура (в порядке первого появления в исходном порядке Rubi); под ним — точные
; сигнатуры с упорядоченными списками правил (файл#номер)
(define (au-print-tree ch)
  (let* ((recs (filter (lambda (r) (equal? (au-f r 3) ch)) (au-records)))
         (leaves (au-uniq (map (lambda (r) (au-f r 5)) recs))))
    (display (string-append "# Дерево сигнатур главы " ch ": правил " (number->string (length recs))
                            ", листьев " (number->string (length leaves))
                            " (лист — грубая сигнатура в порядке первого правила; в листе — точные сигнатуры и id правил в порядке Rubi)"))
    (newline)
    (for-each
     (lambda (lf)
       (let* ((sel (filter (lambda (r) (equal? (au-f r 5) lf)) recs))
              (fines (au-uniq (map (lambda (r) (au-f r 6)) sel))))
         (newline)
         (display (string-append "[" lf "]  правил " (number->string (length sel)) "  разделов "
                                 (number->string (length (au-uniq (map (lambda (r) (au-f r 4)) sel))))))
         (newline)
         (for-each
          (lambda (fn)
            (let ((s2 (filter (lambda (r) (equal? (au-f r 6) fn)) sel)))
              (display (string-append "  " fn " (" (number->string (length s2)) "): "
                                      (au-join (map (lambda (r) (substring (au-f r 0) 5 (string-length (au-f r 0)))) s2) " ")))
              (newline)))
          fines)))
     leaves)))

; крупнейшие листья: «сигнатура<TAB>число правил<TAB>глава»
(define (au-print-leaves)
  (display "chapter\tsignature\trules")
  (newline)
  (for-each
   (lambda (ch)
     (let* ((recs (filter (lambda (r) (equal? (au-f r 3) ch)) (au-records)))
            (leaves (au-uniq (map (lambda (r) (au-f r 5)) recs)))
            (cnt (lambda (lf) (au-count (lambda (r) (equal? (au-f r 5) lf)) recs))))
       (for-each (lambda (lf) (au-tsv-line (list ch lf (cnt lf))))
                 (sort leaves (lambda (a b) (> (cnt a) (cnt b)))))))
   '("1" "4")))

; ---------- самопроверка: пример FUZZ ----------
; Пример правила (rubi::fz-example) классифицируется той же функцией; несовпадение грубой сигнатуры — дефект
; классификатора ИЛИ неизбежная подстановка (произвольные ?u/?Pq заменены конкретными выражениями; n = 2 у ?n
; делает bin -> bin2; ноль коэффициента роняет член суммы). Выход: id, sig(образец), sig(пример), класс.
(define (au-has-arb? p)
  (cond ((au-arb-var? p) #t)
        ((pair? p) (any? au-has-arb? p))
        (else #f)))

(define (au-mismatch-class pat psig esig)
  (cond ((au-has-arb? pat) "arb-substituted")
        ((equal? esig "unclassified") "example-unclassified")
        (else "other")))

(define (au-relaxed-equal? pat ex)
  (set! au-relaxed #t)
  (let ((same (equal? (nth (au-classify pat) 0) (nth (au-classify ex) 0))))
    (set! au-relaxed #f)
    same))

; «Пример частный»: FUZZ подставил конкретный ?n/коэффициент, и множитель сузился (bin -> lin/bin2/quad,
; trin -> sum[...]/quad/lin, показатель e -> число). Образец сужаемых типов P, пример — из P, lin или sum[...].
(define au-narrow-pat '("bin" "bin2" "trin" "bin-gen" "trin-gen" "quad"))
(define (au-strip-e s) (au-join (string-split s "^e") ""))
(define (au-narrow-ex? s)
  (or (member? s au-narrow-pat) (equal? s "lin")
      (and (> (string-length s) 4) (equal? (substring s 0 4) "sum["))))
(define (au-remove-one x l)
  (cond ((null? l) '())
        ((equal? x (car l)) (cdr l))
        (else (cons (car l) (au-remove-one x (cdr l))))))
(define (au-subtract fixed l)               ; l без элементов fixed, или #f если какого-то нет
  (cond ((null? fixed) l)
        ((not (member? (car fixed) l)) #f)
        (else (au-subtract (cdr fixed) (au-remove-one (car fixed) l)))))
(define (au-narrowing? pat ex)
  (let* ((pf (map (lambda (p) (au-strip-e (car p))) (au-factor-types pat)))
         (ef (map (lambda (p) (au-strip-e (car p))) (au-factor-types ex)))
         (fixed (filter (lambda (s) (not (member? s au-narrow-pat))) pf))
         (nar (filter (lambda (s) (member? s au-narrow-pat)) pf))
         (rest (au-subtract fixed ef)))
    (and rest (= (length rest) (length nar)) (every? au-narrow-ex? rest))))

(define (au-selfcheck-rule r)
  (let* ((c (au-classify (nth r 2)))
         (gen (try (rubi::fz-example r) (lambda (e) (list 'error)))))
    (if (not (equal? (car gen) 'ok))
        (list (nth r 1) (nth c 0) "-" "no-example")
        (let* ((ec (au-classify (cadr gen))))
          (list (nth r 1) (nth c 0) (nth ec 0)
                (cond ((equal? (nth c 0) "unclassified") "pattern-unclassified")
                      ((equal? (nth c 0) (nth ec 0)) "match")
                      ((au-relaxed-equal? (nth r 2) (cadr gen)) "match-bin2")
                      (else
                       (let ((m (au-mismatch-class (nth r 2) (nth c 0) (nth ec 0))))
                         (if (and (equal? m "other") (try (au-narrowing? (nth r 2) (cadr gen)) (lambda (e) #f)))
                             "special-narrow"
                             m)))))))))

; (au-selfcheck-run step offset): каждое step-е правило глав 1 и 4 начиная с offset (выборка равномерная по порядку Rubi)
(define (au-selfcheck-run step offset)
  (load "lib/rubi/fuzz.lisp")
  (set! rubi::*rubi-tries-limit* 6000)
  (display "id\tpattern_sig\texample_sig\tstatus")
  (newline)
  (let loop ((l (sort (au-rules) (lambda (a b) (< (nth a 0) (nth b 0))))) (i 0))
    (if (pair? l)
        (begin
          (if (= (modulo i step) offset)
              (au-tsv-line (au-selfcheck-rule (car l))))
          (loop (cdr l) (+ i 1))))))

(define (au-table what)
  (cond ((equal? what "signatures") (au-print-signatures))
        ((equal? what "coverage") (au-print-coverage))
        ((equal? what "reasons") (au-print-reasons))
        ((equal? what "leaves") (au-print-leaves))
        ((equal? what "tree-1") (au-print-tree "1"))
        ((equal? what "tree-4") (au-print-tree "4"))
        ((equal? what "shadow-1") (au2-print-shadow "1"))
        ((equal? what "shadow-4") (au2-print-shadow "4"))
        ((equal? what "arb") (au2-print-arb))
        ((equal? what "recognizers-1") (au2-print-recognizers "1" #t))
        ((equal? what "recognizers-4") (au2-print-recognizers "4" #t))
        ((equal? what "recognizers-4-nogrid") (au2-print-recognizers "4" #f))
        ((equal? what "pairs-1") (set! au2-grid-on #f) (au2-print-shadow "1"))
        ((equal? what "pairs-4") (set! au2-grid-on #f) (au2-print-shadow "4"))
        (else (error "au-table: неизвестная таблица" what))))

; =====================================================================================================
; RUBI.AUDIT.2 — дубли, вложение образцов, затенение (часть 1: дубли и вложение)
; =====================================================================================================
; Лист = грубая сигнатура шага 1 (в пределах главы). Для пары (A, B) в листе, A раньше B по порядку Rubi:
;   вложение A ⊇ B — ac-match образца A против образца B, где переменные B заменены константами K_имя
;     (образец B с необязательной ?v. дополнительно проверяется с ?v. := значение по умолчанию — 0 в сумме,
;     1 в произведении и показателе: A обязан взять и такие частные случаи);
;   дубль — вложение в обе стороны и условия совпадают при переименовании переменных (по θ_AB) в обе стороны.
; Правила с функцией-переменной (?F x) в образце (ac-match их не поддерживает) в пары не входят — см. распознаватели.

(define (au2-const-name v) (string->symbol (string-append "K_" (au-vname v))))

(define (au2-freeze e)
  (cond ((au-pvar? e) (au2-const-name e))
        ((pair? e) (map au2-freeze e))
        (else e)))

; подстановка привязок ((?v значение) ...) в выражение; (quote ...) не трогается
(define (au2-subst p alst)
  (cond ((symbol? p) (let ((b (assoc p alst))) (if b (cadr b) p)))
        ((pair? p) (if (equal? (car p) (quote quote)) p (map (lambda (t) (au2-subst t alst)) p)))
        (else p)))

(define (au2-mentions? e v)
  (cond ((equal? e v) #t)
        ((pair? e) (any? (lambda (t) (au2-mentions? t v)) e))
        (else #f)))

; необязательные переменные образца: ?v. (имя оканчивается точкой), без повторов
(define (au2-optional-vars p)
  (au-uniq
   (let walk ((e p))
     (cond ((au-pvar? e)
            (let ((s (au-sym-name e))) (if (equal? (substring s (- (string-length s) 1) (string-length s)) ".") (list e) '())))
           ((pair? e) (append-map walk e))
           (else '())))))

(define (au2-var-eq? t v) (and (au-pvar? t) (equal? (au-vname t) (au-vname v))))

; образец с ?v. := значение по умолчанию (в сумме — слагаемое пропадает, в произведении и показателе — множитель);
; #f, если ?v. стоит где-то ещё
(define (au2-defaultize e v)
  (let ((r (au2-dz e v)))
    (if (au2-has-var? r v) #f r)))

(define (au2-has-var? e v)
  (cond ((au-pvar? e) (au2-var-eq? e v))
        ((pair? e) (any? (lambda (t) (au2-has-var? t v)) e))
        (else #f)))

(define (au2-dz e v)
  (cond ((not (pair? e)) e)
        ((equal? (car e) '+)
         (let ((ts (filter (lambda (t) (not (au2-var-eq? t v))) (map (lambda (t) (au2-dz t v)) (cdr e)))))
           (cond ((null? ts) 0) ((null? (cdr ts)) (car ts)) (else (cons '+ ts)))))
        ((equal? (car e) '*)
         (let ((ts (filter (lambda (t) (not (au2-var-eq? t v))) (map (lambda (t) (au2-dz t v)) (cdr e)))))
           (cond ((null? ts) 1) ((null? (cdr ts)) (car ts)) (else (cons '* ts)))))
        ((and (equal? (car e) '^) (= (length e) 3) (au2-var-eq? (caddr e) v)) (au2-dz (cadr e) v))
        (else (map (lambda (t) (au2-dz t v)) e))))

; экземпляры образца B для проверки вложения: сам B и по одному «частному» на каждую необязательную переменную
(define (au2-instances pat)
  (cons (au2-freeze pat)
        (filter (lambda (x) x)
                (map (lambda (v) (let ((d (au2-defaultize pat v))) (and d (au2-freeze d))))
                     (au2-optional-vars pat)))))

; θ: привязки переменных A к выражениям над константами B, либо #f; ошибки сопоставителя — #f
(define (au2-match r inst)
  (try (ac-match-prepared (rubi::rubi-prepared r) (rubi::rubi-norm-form inst) #f) (lambda (e) #f)))

(define (au2-contains ra b-insts)
  (let ((th (au2-match ra (car b-insts))))
    (and th
         (every? (lambda (i) (au2-match ra i)) (cdr b-insts))
         th)))

; ---------- условия: разрешимый фрагмент и синтаксическое следование ----------
; Условие правила = конъюнкция атомов. Атом разбирается в примитивы: (eq E) (ne E) [E с точностью до знака],
; (gt E) (ge E) [E > 0, E >= 0], (int a) (rat a) (frac a), (nint a) (nrat a), (or конъюнкция ...), (opq текст) —
; утилита вне разрешимого фрагмента. Параметры считаются вещественными (¬(E>0) ⇔ E<=0). Разрешимый фрагмент:
; FreeQ, EqQ, NeQ, GtQ, LtQ, GeQ, LeQ, IGtQ, ILtQ, IntegerQ, IntegersQ, RationalQ, FractionQ, PosQ, NegQ, not/or/and.
; Следование B ⇒ A — только достаточное (синтаксическое включение + сдвиги на константу): неполное, но не ложное.

(define (au2-nrm e) (try (simplify (expand e)) (lambda (x) e)))

(define (au2-op-name op)
  (let* ((s (to-string op)) (p "rubi::rubi-"))
    (if (and (> (string-length s) 11) (equal? (substring s 0 11) p)) (substring s 11 (string-length s)) s)))

(define (au2-sgn e)                          ; E или -E — что меньше по записи
  (let ((m (au2-nrm (list '- 0 e))))
    (if (string<? (to-string m) (to-string e)) m e)))

(define (au2-xfree? e) (not (au2-mentions? e 'x)))

(define (au2-sub e c) (au2-nrm (list '- e c)))

(define (au2-prim-eq e) (if (number? e) (if (= e 0) '() (list '(false))) (list (list 'eq (au2-sgn e)))))
(define (au2-prim-ne e) (if (number? e) (if (= e 0) (list '(false)) '()) (list (list 'ne (au2-sgn e)))))
(define (au2-prim-gt e) (if (number? e) (if (> e 0) '() (list '(false))) (list (list 'gt e))))
(define (au2-prim-ge e) (if (number? e) (if (>= e 0) '() (list '(false))) (list (list 'ge e))))
(define (au2-prim-int a) (if (number? a) (if (integer? a) '() (list '(false))) (list (list 'int a))))
(define (au2-prim-rat a) (if (number? a) '() (list (list 'rat a))))

; аргументы атома; у одноаргументного сравнения (NeQ[E], EqQ[E]) второй аргумент — 0
(define (au2-args atom) (if (and (pair? (cdr atom)) (null? (cddr atom))) (append (cdr atom) (list 0)) (cdr atom)))

(define (au2-parse atom)
  (cond
    ((not (pair? atom)) (if (equal? atom #t) '() (list (list 'opq (to-string atom)))))
    ((equal? (car atom) 'and) (append-map au2-parse (cdr atom)))
    ((equal? (car atom) 'or)
     (let ((ds (map au2-parse (cdr atom))))
       (cond ((any? null? ds) '())
             (else (let ((ds2 (filter (lambda (d) (not (equal? d '((false))))) ds)))
                     (cond ((null? ds2) (list '(false)))
                           ((null? (cdr ds2)) (car ds2))
                           (else (list (cons 'or ds2)))))))))
    ((equal? (car atom) 'not) (au2-negate (au2-parse (cadr atom)) atom))
    (else
     (let ((op (au2-op-name (car atom))) (as (au2-args atom)))
       (cond
         ((equal? op "freeq")
          (let ((vs (if (and (pair? (car as)) (equal? (car (car as)) 'list)) (cdr (car as)) (list (car as)))))
            (if (every? au2-xfree? vs) '() (list '(false)))))
         ((equal? op "eqq") (au2-prim-eq (au2-sub (car as) (cadr as))))
         ((equal? op "neq") (au2-prim-ne (au2-sub (car as) (cadr as))))
         ((equal? op "gtq") (au2-prim-gt (au2-sub (car as) (cadr as))))
         ((equal? op "ltq") (au2-prim-gt (au2-sub (cadr as) (car as))))
         ((equal? op "geq") (au2-prim-ge (au2-sub (car as) (cadr as))))
         ((equal? op "leq") (au2-prim-ge (au2-sub (cadr as) (car as))))
         ((equal? op "posq") (au2-prim-gt (au2-nrm (car as))))
         ((equal? op "negq") (au2-prim-gt (au2-nrm (list '- 0 (car as)))))
         ((equal? op "igtq")
          (append (au2-prim-int (au2-nrm (car as))) (au2-prim-gt (au2-sub (car as) (cadr as)))))
         ((equal? op "iltq")
          (append (au2-prim-int (au2-nrm (car as))) (au2-prim-gt (au2-sub (cadr as) (car as)))))
         ((equal? op "integerq") (au2-prim-int (au2-nrm (car as))))
         ((equal? op "integers-q") (append-map (lambda (a) (au2-prim-int (au2-nrm a))) as))
         ((equal? op "rationalq") (au2-prim-rat (au2-nrm (car as))))
         ((equal? op "fractionq")
          (let ((a (au2-nrm (car as)))) (if (number? a) (if (integer? a) (list '(false)) '()) (list (list 'frac a)))))
         (else (list (list 'opq (to-string atom)))))))))

; ¬(конъюнкция): одиночный примитив — двойственный, иначе — непрозрачный
(define (au2-negate prims atom)
  (cond ((null? prims) (list '(false)))
        ((equal? prims '((false))) '())
        ((not (null? (cdr prims))) (list (list 'opq (to-string atom))))
        (else
         (let ((p (car prims)))
           (cond ((equal? (car p) 'eq) (list (list 'ne (cadr p))))
                 ((equal? (car p) 'ne) (list (list 'eq (cadr p))))
                 ((equal? (car p) 'gt) (au2-prim-ge (au2-nrm (list '- 0 (cadr p)))))
                 ((equal? (car p) 'ge) (au2-prim-gt (au2-nrm (list '- 0 (cadr p)))))
                 ((equal? (car p) 'int) (list (list 'nint (cadr p))))
                 ((equal? (car p) 'rat) (list (list 'nrat (cadr p))))
                 (else (list (list 'opq (to-string atom)))))))))

(define (au2-decidable? prims)
  (every? (lambda (p)
            (cond ((equal? (car p) 'opq) #f)
                  ((equal? (car p) 'or) (every? au2-decidable? (cdr p)))
                  (else #t)))
          prims))

(define (au2-cond-conj r)
  (let ((c (car (rubi::rubi-fixed r))))
    (if (or (equal? c #t) (null? c)) '() (rubi::rubi-conjuncts c))))

; примитивы условия правила; θ — привязки переменных (#f — без подстановки)
(define (au2-cond-prims r th)
  (append-map (lambda (a) (au2-parse (if th (au2-subst a th) a))) (au2-cond-conj r)))

; факты, следующие из примитивов B
(define (au2-shifts kind e lo)
  (let loop ((t lo) (acc '()))
    (if (> t 8) acc (loop (+ t 1) (cons (list kind (au2-nrm (list '+ e t))) acc)))))

(define (au2-ne-shifts e lo)
  (let loop ((t lo) (acc '()))
    (if (> t 8) acc (loop (+ t 1) (cons (list 'ne (au2-sgn (au2-nrm (list '+ e t)))) acc)))))

(define (au2-int-shift? e ints)               ; E = a + число для некоторого (int a)?
  (any? (lambda (a) (number? (au2-nrm (list '- e a)))) ints))

(define (au2-facts prims)
  (let ((ints (map cadr (filter (lambda (p) (equal? (car p) 'int)) prims))))
    (au2-uniq
     (append
      prims
      (append-map
       (lambda (p)
         (let ((k (car p)))
           (cond ((equal? k 'gt)
                  (append (au2-shifts 'gt (cadr p) 0) (au2-shifts 'ge (cadr p) 0) (au2-ne-shifts (cadr p) 0)
                          (if (au2-int-shift? (cadr p) ints) (au2-shifts 'ge (cadr p) -1) '())))
                 ((equal? k 'ge)
                  (append (au2-shifts 'ge (cadr p) 0) (au2-shifts 'gt (cadr p) 1) (au2-ne-shifts (cadr p) 1)))
                 ((equal? k 'int) (list (list 'rat (cadr p))))
                 ((equal? k 'frac) (list (list 'rat (cadr p))))
                 (else '()))))
       prims)))))

(define (au2-uniq l) (au-uniq l))

; примитив-требование следует из фактов?
(define (au2-entailed? p facts)
  (cond ((equal? p '(false)) #f)
        ((equal? (car p) 'or)
         (or (member? p facts)
             (any? (lambda (d) (every? (lambda (q) (au2-entailed? q facts)) d)) (cdr p))))
        (else (member? p facts))))

; ---------- пары в листе ----------
(define au2-binfo-cache (make-hash))

; сведения о B: (экземпляры факты разрешимо? примитивы)
(define (au2-binfo b)
  (or (hash-ref au2-binfo-cache (nth b 1) #f)
      (let* ((prims (append-map (lambda (a) (au2-parse (au2-freeze a))) (au2-cond-conj b)))
             (info (list (au2-instances (nth b 2)) (au2-facts prims) (au2-decidable? prims) prims)))
        (hash-set! au2-binfo-cache (nth b 1) info)
        info))) 

(define (au2-head-var-pattern? p)
  (cond ((pair? p) (or (and (au-pvar? (car p)) (not (au-arb-var? (car p)))) (any? au2-head-var-pattern? p)))
        (else #f)))

; анализ пары: список (вид θ решение) или #f, если вложения нет
;   вид: dup | cond-entailed | cond-open | cond-false (условие A ложно на всех экземплярах B: FreeQ от выражения с x или константа)
(define (au2-pair a b)
  (let* ((bi (au2-binfo b))
         (th (au2-contains a (car bi))))
    (if (not th)
        #f
        (let* ((aprims (append-map (lambda (at) (au2-parse (au2-subst at th))) (au2-cond-conj a)))
               (facts (cadr bi)))
          (cond
            ((member? '(false) aprims) (list "cond-false" th #f))
            (else
             (let* ((entailed (every? (lambda (p) (au2-entailed? p facts)) aprims))
                    (decid (and (au2-decidable? aprims) (caddr bi)))
                    (back (and entailed (au2-dup-back a b bi))))
               (cond (back (list "dup" th decid))
                     (entailed (list "cond-entailed" th decid))
                     (else (list "cond-open" th decid))))))))))

; обратное вложение B ⊇ A и условие B ⇒ условие A: вместе с прямым — дубль
(define (au2-dup-back a b bi)
  (let* ((ai (au2-binfo a))
         (th2 (au2-contains b (car ai))))
    (and th2
         (let ((bprims (append-map (lambda (bt) (au2-parse (au2-subst bt th2))) (au2-cond-conj b))))
           (and (not (member? '(false) bprims))
                (every? (lambda (p) (au2-entailed? p (cadr ai))) bprims))))))

; листья главы: ((лист . правила-по-порядку) ...), без unclassified
(define (au2-leaves ch)
  (let* ((recs (filter (lambda (r) (and (equal? (au-f r 3) ch) (not (equal? (au-f r 5) "unclassified")))) (au-records)))
         (byid (make-hash))
         (rules (au-rules)))
    (for-each (lambda (r) (hash-set! byid (nth r 1) r)) rules)
    (map (lambda (lf)
           (cons lf (map (lambda (rc) (hash-ref byid (au-f rc 0) #f))
                         (filter (lambda (rc) (equal? (au-f rc 5) lf)) recs))))
         (au-uniq (map (lambda (r) (au-f r 5)) recs)))))

(define (au2-lid r) (nth r 1))

; (au2-shadow-run ch): по листу — все пары A < B; строки: leaf, A, B, вид, разрешимо, порядки; итоги листа — «# leaf …»
; Строки печатаются сразу (прогон можно прервать без потерь); возвращается список итогов листьев.
; Сетка: все пары dup и cond-entailed и каждая au2-sample-k-я пара cond-open; остальные — «not-gridded».
(define au2-sample-k 8)

(define (au2-print-row ch lf a b res v)
  (au-tsv-line (list ch lf (nth a 1) (nth b 1) (nth v 0) (car res) (if (nth res 2) "yes" "no")
                     (nth v 3) (nth v 4) (nth a 0) (nth b 0) (nth v 1) (nth v 2))))

(define (au2-stream-rows ch)
  (let ((stats '()) (open-n 0))
    (for-each
     (lambda (lf)
       (let ((pairs 0) (contained 0) (xb 0))
         (for-each
          (lambda (a)
            (if (not (au2-head-var-pattern? (nth a 2)))
                (for-each
                 (lambda (b)
                   (if (and (> (nth b 0) (nth a 0)) (not (au2-head-var-pattern? (nth b 2))))
                       (let ((res (au2-pair a b)))
                         (set! pairs (+ pairs 1))
                         (if res
                             (if (equal? (car res) "cond-false")
                                 (set! xb (+ xb 1))
                                 (let ((grid? (and au2-grid-on
                                                   (or (not (equal? (car res) "cond-open"))
                                                       (begin (set! open-n (+ open-n 1))
                                                              (= (modulo open-n au2-sample-k) 0))))))
                                   (set! contained (+ contained 1))
                                   (au2-print-row ch (car lf) a b res
                                                  (cond (grid? (au2-verdict a b res))
                                                        (au2-grid-on (list "not-gridded" "-" "-" 0 0))
                                                        (else (list (car res) "-" "-" 0 0))))))))))
                 (cdr lf))))
          (cdr lf))
         (set! stats (cons (list (car lf) (length (cdr lf)) pairs contained xb) stats))))
     (au2-leaves ch))
    (reverse stats)))

; печать: строки таблицы; итоги листьев — «#leaf <лист> <правил> <пар> <вложений> <cond-false>» (node считает по ним свод)
(define au2-grid-on #t)
(define (au2-verdict a b res)
  (if au2-grid-on
      (au2-grid-verdict a b (car res) (nth res 2))
      (list (car res) "-" "-" 0 0)))

(define (au2-print-shadow ch)
  (let ((res '()))
    (display "chapter	leaf	A	B	kind	cond_kind	decidable	points	fired	ord_A	ord_B	example	witness")
    (newline)
    (set! res (au2-stream-rows ch))
    (for-each (lambda (s) (au-tsv-line (cons "#leaf" s))) res)))

; =====================================================================================================
; RUBI.AUDIT.2 (часть 2): затенение по сетке параметров
; =====================================================================================================
; Для вложенной пары (A ⊇ B, A раньше B): точки сетки — привязки параметров B, при которых условие B истинно
; (генератор — lib/rubi/fuzz.lisp: пулы значений, подъём по условию fz-refine; показатели {-2,-1,-1/2,0,1/2,1,2,3,5,7,
; 3/7,-5/3, символ zz}, коэффициенты {0,±1,±2,3,1/2}, связки b c - a d = 0 и m + n + 2 = 0 — подъёмом). Пример = образец B с
; точкой; «A срабатывает» = реальный ac-match-prepared A на нормализованном примере с условием A (как в движке).
;   dup               — вложение в обе стороны + условия совпадают (синтаксически, при переименовании)
;   subsumed-proved   — вложение + условия обоих правил целиком из разрешимого фрагмента + B ⇒ A доказано
;                       синтаксически + на сетке есть пример, где A срабатывает, и нет точки, где не срабатывает
;   subsumed-grid     — вложение + на ≥ 3 точках сетки A срабатывает везде, нет контрпримера (доказательства нет)
;   nested-open       — A срабатывает не на всех точках (контрпример в колонке witness)
;   independent       — A не срабатывает ни на одной точке B (≥ 3), вложение образцов пусто по условию
;   nested-nogrid     — точек сетки < 3 (или < 1): вывода нет
;   proof-conflict    — доказано синтаксически, но на сетке есть контрпример (дефект анализа, ожидается 0)

(define au2-fuzz-loaded #f)
(define (au2-ensure-fuzz)
  (if (not au2-fuzz-loaded)
      (begin (load (string-append (if (bound? 'au-root-pre) (eval 'au-root-pre) "") "lib/rubi/fuzz.lisp"))
             (set! au2-fuzz-loaded #t))))

(define au2-exp-pool '(2 1 3 -1 -2 -1/2 1/2 0 5 7 3/7 -5/3 zz))
(define au2-coef-pool '(2 3 1 -1 0 1/2 -2))
(define au2-poly-pool '((+ 1 x) (^ x 2) (+ 1 (* 2 x) (^ x 3)) 3))

(define (au2-pool v cond0)
  (let ((n (rubi::fz-name v)))
    (cond ((equal? n "x") '(x))
          ((au-poly-var? v) au2-poly-pool)
          ((member? n '("F" "G" "H")) '(2 3 1/2))      ; основание показательной функции (^ ?F …): положительные числа
          ((rubi::fz-hint (rubi::fz-strip-dot v) cond0) (rubi::fz-pool v cond0))
          ((au-arb-var? v) (rubi::fz-pool v cond0))
          ((member? n '("m" "n" "p" "q" "r" "k" "j" "i" "l")) au2-exp-pool)
          (else au2-coef-pool))))

; псевдослучайный выбор: (au2-lcg s) -> следующее состояние
(define (au2-lcg s) (modulo (+ (* s 1103515245) 12345) 2147483648))

(define (au2-sample vars pools s)            ; -> (привязки . новое состояние)
  (let loop ((vs vars) (ps pools) (s s) (acc '()))
    (if (null? vs)
        (cons (reverse acc) s)
        (let* ((s2 (au2-lcg s)) (pool (cdr (car ps))) (k (modulo (quotient s2 65536) (length pool))))
          (loop (cdr vs) (cdr ps) s2 (cons (list (rubi::fz-strip-dot (car vs)) (nth pool k)) acc))))))

; подстановка с переменными в образце (?a. -> ключ ?a)
(define (au2-inst p alst)
  (cond ((symbol? p) (let ((b (assoc (rubi::fz-strip-dot p) alst))) (if b (cadr b) p)))
        ((pair? p) (if (equal? (car p) 'quote) p (map (lambda (t) (au2-inst t alst)) p)))
        (else p)))

(define (au2-fires? a ex)
  (let ((m (try (ac-match-prepared (rubi::rubi-prepared a) (rubi::rubi-norm-form ex) (rubi::rubi-cond-fn a))
                (lambda (e) #f))))
    (if m #t #f)))

(define au2-pts-cache (make-hash))
(define au2-max-pts 8)
(define au2-cands 60)

; точки сетки для B: список примеров — образец B с точкой (проверено: B на нём срабатывает по своему образцу и условию)
(define (au2-points b)
  (or (hash-ref au2-pts-cache (nth b 1) #f)
      (let* ((pat (nth b 2)) (cf (rubi::rubi-cond-fn b)) (cond0 (car (rubi::rubi-fixed b)))
             (vars (rubi::fz-pvars pat '()))
             (pools (map (lambda (v) (cons (rubi::fz-strip-dot v) (au2-pool v cond0))) vars))
             (nconj (length (au2-cond-conj b)))
             (score (lambda (bd) (if cf (rubi::fz-score b cf bd) 999)))
             (seed (let ((g (try (rubi::fz-example b) (lambda (e) '(none))))) (if (equal? (car g) 'ok) (list (caddr g)) '())))
             (pts
              (let loop ((i 0) (s (+ 12345 (* 7919 (nth b 0)))) (acc seed))
                (if (or (>= i au2-cands) (>= (length acc) au2-max-pts))
                    (reverse acc)
                    (let* ((sm (au2-sample vars pools s)) (bd (car sm)) (sc (score bd)))
                      (cond ((>= sc 999) (loop (+ i 1) (cdr sm) (if (member? bd acc) acc (cons bd acc))))
                            ((and cf (>= sc (max 1 (- nconj 1))))
                             (let ((rf (rubi::fz-refine b cond0 cf bd pools vars)))
                               (loop (+ i 1) (cdr sm)
                                     (if (and (>= (cadr rf) 999) (not (member? (car rf) acc))) (cons (car rf) acc) acc))))
                            (else (loop (+ i 1) (cdr sm) acc)))))))
             (exs (filter (lambda (p) p)
                          (map (lambda (bd)
                                 (let ((ex (au2-inst pat bd)))
                                   (and (au2-fires? b ex) (list ex bd))))
                               pts))))
        (hash-set! au2-pts-cache (nth b 1) exs)
        exs)))

; решение по сетке: (вид пример-где-A-срабатывает контрпример-где-нет число-точек срабатываний)
(define (au2-grid-verdict a b kind decidable)
  (au2-ensure-fuzz)
  (let* ((pts (au2-points b))
         (n (length pts))
         (fired (filter (lambda (p) (au2-fires? a (car p))) pts))
         (nf (length fired))
         (miss (filter (lambda (p) (not (member? p fired))) pts))
         (ex (if (pair? fired) (to-string (car (car fired))) "-"))
         (wit (if (pair? miss) (to-string (car (car miss))) "-"))
         (proved-syn (and (equal? kind "cond-entailed") decidable)))
    (list
     (cond ((equal? kind "dup") "dup")
           ((and proved-syn (> nf 0) (= nf n)) "subsumed-proved")
           ((and proved-syn (> nf 0) (< nf n)) "proof-conflict")
           ((and (>= n 3) (= nf n)) "subsumed-grid")
           ((and (>= n 3) (= nf 0)) "independent")
           ((and (>= n 3) (< nf n)) "nested-open")
           (else "nested-nogrid"))
     ex wit n nf)))

; =====================================================================================================
; RUBI.AUDIT.2 (часть 3): класс остатка ?u — сигнатура второго уровня
; =====================================================================================================
; Для правил с произвольной переменной (?u ?v ?w ?y ?z ?Fx — тип u шага 1; ?Pq/?Qx/?Rn — уже тип Pq) из условия берётся
; предикат на неё. Иерархия классов: const ⊂ poly ⊂ rational ⊂ algebraic ⊂ trig/exp ⊂ other; у переменной берётся самый
; узкий найденный класс; нет предиката или предикат не про класс (NonsumQ, MatchQ, InertTrigFreeQ, …) — other.
; Сигнатура 2 = сигнатура 1 + «|классы» (классы переменных по алфавиту имён): lin*u -> lin*u|poly.

(define au2-class-order '("const" "poly" "rational" "algebraic" "trig/exp" "other"))

(define au2-pred-table
  '(("freeq" "const") ("independent-q" "const")
    ("linear-q" "poly" "lin") ("linear-match-q" "poly" "lin") ("linear-pair-q" "poly" "lin") ("int-linear-q" "poly" "lin")
    ("quadratic-q" "poly" "quad") ("quadratic-match-q" "poly" "quad") ("int-quadratic-q" "poly" "quad")
    ("binomial-q" "poly" "bin") ("binomial-match-q" "poly" "bin") ("int-binomial-q" "poly" "bin")
    ("generalized-binomial-q" "poly" "bin") ("generalized-binomial-match-q" "poly" "bin") ("pseudo-binomial-pair-q" "poly" "bin")
    ("trinomial-q" "poly" "trin") ("trinomial-match-q" "poly" "trin")
    ("generalized-trinomial-q" "poly" "trin") ("generalized-trinomial-match-q" "poly" "trin")
    ("poly-q" "poly" "poly") ("polynomialq" "poly" "poly") ("monomial-q" "poly" "poly")
    ("quotient-of-linears-q" "rational" "quot-lin") ("rational-function-q" "rational" "rat")
    ("algebraic-function-q" "algebraic" "alg")
    ("function-of-trig-of-linear-q" "trig/exp" "func-trig") ("known-sine-integrand-q" "trig/exp" "known-trig")
    ("known-secant-integrand-q" "trig/exp" "known-trig") ("known-tangent-integrand-q" "trig/exp" "known-trig")
    ("known-cotangent-integrand-q" "trig/exp" "known-trig")
    ("nonsum-q" "other" "nonsum") ("sumq" "other" "sum") ("matchq" "other" "matchq") ("inert-trig-free-q" "other" "inert-free")
    ("inverse-function-free-q" "other" "inv-free") ("trig-simplify-q" "other" "trig-simp") ("falseq" "other" "falseq")))

(define (au2-strip-dot v)
  (let ((s (au-sym-name v)))
    (if (and (> (string-length s) 1) (equal? (substring s (- (string-length s) 1) (string-length s)) "."))
        (string->symbol (substring s 0 (- (string-length s) 1)))
        v)))

(define (au2-arb-vars pat)
  (au-uniq
   (let walk ((e pat))
     (cond ((and (au-pvar? e) (au-arb-var? e) (not (au-poly-var? e))) (list (au2-strip-dot e)))
           ((pair? e) (append-map walk e))
           (else '())))))

(define (au2-class-index c) (let loop ((l au2-class-order) (i 0)) (if (equal? (car l) c) i (loop (cdr l) (+ i 1)))))

; (класс предикат) для переменной v правила r
(define (au2-var-class r v)
  (let* ((atoms (au2-cond-conj r))
         (found (filter (lambda (x) x)
                        (map (lambda (a)
                               (and (pair? a) (symbol? (car a)) (au2-mentions? (cdr a) v)
                                    (let ((e (assoc (au2-op-name (car a)) au2-pred-table)))
                                      (and e (cdr e)))))
                             atoms))))
    (if (null? found)
        (list "other" "no-predicate")
        (let ((best (car (sort found (lambda (p q) (< (au2-class-index (car p)) (au2-class-index (car q))))))))
          (list (car best) (if (null? (cdr best)) (car best) (cadr best)))))))

; (классы-через-запятую предикаты) или #f, если у правила нет произвольной переменной
(define (au2-arb-info r)
  (let ((vs (au2-arb-vars (nth r 2))))
    (and (pair? vs)
         (let ((cs (map (lambda (v) (cons (au-sym-name v) (au2-var-class r v))) vs)))
           (list (au-join (map (lambda (c) (nth c 1)) (sort cs (lambda (a b) (string<? (car a) (car b))))) ",")
                 (au-join (map (lambda (c) (string-append (car c) ":" (nth c 2))) cs) ","))))))

; записи «правило: id, глава, сигнатура 1, сигнатура 2, классы, предикаты»
(define (au2-sig2-records)
  (let ((byid (make-hash)))
    (for-each (lambda (r) (hash-set! byid (nth r 1) r)) (au-rules))
    (map (lambda (rc)
           (let* ((r (hash-ref byid (au-f rc 0) #f))
                  (info (and (not (equal? (au-f rc 5) "unclassified")) (au2-arb-info r))))
             (list (au-f rc 0) (au-f rc 3) (au-f rc 4) (au-f rc 5)
                   (if info (string-append (au-f rc 5) "|" (nth info 0)) (au-f rc 5))
                   (if info (nth info 0) "-") (if info (nth info 1) "-"))))
         (au-records))))

(define (au2-print-arb)
  (display "id\tchapter\tsection\tsignature\tsignature2\tclasses\tpredicates")
  (newline)
  (for-each au-tsv-line (au2-sig2-records)))

; =====================================================================================================
; RUBI.AUDIT.2 (часть 4): распознаватели — правила-подстановки без структуры образца
; =====================================================================================================
; Узел «recognizer»: образец без типизированных множителей x (только u/Pq/константы) либо с функцией-переменной (?F x),
; и при этом условие или правая часть опираются на распознавание: FunctionOfTrig/FunctionOfTrigOfLinearQ,
; DerivativeDivides, TryPureTanSubst в условии либо SubstFor/Subst/SubstPower в правой части.
; Правила со структурным образцом, у которых условие содержит ту же утилиту, помечены struct+recognizer, с подстановкой
; только в правой части — struct+subst (структурные узлы; в счёт распознавателей не входят).
; Вложение образцов для распознавателей не считается: вместо него — затенение на сетке (распознаватель A раньше структурного
; B своего раздела: срабатывает ли A на примерах B с условием A).

(define au2-rec-cond-utils
  '(("function-of-trig-of-linear-q" "FunctionOfTrigOfLinearQ") ("function-of-trig" "FunctionOfTrig")
    ("derivative-divides" "DerivativeDivides") ("try-pure-tan-subst" "TryPureTanSubst")))
(define au2-rec-rhs-utils
  '(("subst-for" "SubstFor") ("subst-pat" "Subst") ("subst" "Subst") ("subst-power" "SubstPower")
    ("function-of-trig" "FunctionOfTrig") ("derivative-divides" "DerivativeDivides")
    ("try-pure-tan-subst" "TryPureTanSubst")))

; имена голов (все списки, включая вложенные), без повторов
(define (au2-heads e)
  (au-uniq
   (let walk ((e e))
     (cond ((pair? e) (append (if (symbol? (car e)) (list (au2-op-name (car e))) '()) (append-map walk e)))
           (else '())))))

(define (au2-utils-in table e)
  (let ((hs (au2-heads e)))
    (au-uniq (filter (lambda (x) x) (map (lambda (p) (and (member? (car p) hs) (cadr p))) table)))))

; чистый образец: все типы множителей — только u/Pq (константы отброшены), либо голова-переменная
(define (au2-pure-sig? sig)
  (or (equal? sig "K")
      (every? (lambda (s) (member? s '("u" "Pq"))) (string-split sig "*"))))

; (вид утилиты) правила: вид — recognizer | struct+recognizer | struct+subst | -
(define (au2-rec-kind r rc)
  (let* ((body (rubi::rubi-fixed r))
         (cu (au2-utils-in au2-rec-cond-utils (car body)))
         (ru (au2-utils-in au2-rec-rhs-utils (cdr body)))
         (hv (au2-head-var-pattern? (nth r 2)))
         (all (au-uniq (append (if hv (list "?F") '()) cu ru)))
         (pure (or hv (au2-pure-sig? (au-f rc 5)))))
    (cond ((and pure (or hv (pair? cu) (pair? ru))) (list "recognizer" all))
          ((pair? cu) (list "struct+recognizer" all))
          ((pair? ru) (list "struct+subst" all))
          (else (list "-" '())))))

; записи: (rule rc вид утилиты)
(define (au2-rec-records)
  (let ((byid (make-hash)))
    (for-each (lambda (r) (hash-set! byid (nth r 1) r)) (au-rules))
    (map (lambda (rc)
           (let* ((r (hash-ref byid (au-f rc 0) #f)) (k (au2-rec-kind r rc)))
             (list r rc (car k) (cadr k))))
         (au-records))))

(define au2-rec-minpts 3)
; затенение распознавателя проверяется на ближайших au2-rec-cap структурных правилах своего раздела, стоящих дальше по порядку (выборка)
(define au2-rec-cap 100)

; затенение распознавателя A структурными правилами B своего раздела, стоящими дальше по порядку: (n-на-всех-точках n-на-части список-B)
(define (au2-rec-shadow a section-bs)
  (au2-ensure-fuzz)
  (set! rubi::*rubi-tries-limit* 3000)       ; сопоставление с ?F и условия на FunctionOf… без ограничения могут не завершиться
  (let loop ((l section-bs) (all 0) (some 0) (alls '()))
    (if (null? l)
        (list all some (reverse alls))
        (let* ((b (car l)) (pts (au2-points b)) (n (length pts)))
          (if (< n au2-rec-minpts)
              (loop (cdr l) all some alls)
              (let ((nf (length (filter (lambda (p) (au2-fires? a (car p))) pts))))
                (cond ((= nf n) (loop (cdr l) (+ all 1) some (cons b alls)))
                      ((> nf 0) (loop (cdr l) all (+ some 1) alls))
                      (else (loop (cdr l) all some alls)))))))))

(define (au2-print-recognizers ch grid?)
  (let* ((recs (filter (lambda (x) (equal? (au-f (nth x 1) 3) ch)) (au2-rec-records)))
         (structural (filter (lambda (x) (and (not (equal? (nth x 2) "recognizer"))
                                              (not (equal? (au-f (nth x 1) 5) "unclassified"))))
                             recs)))
    (display "chapter\tsection\tid\tord\tkind\tutilities\tstructural_before\tstructural_after\tposition\tshadows_all\tshadows_some\tshadowed_examples")
    (newline)
    (for-each
     (lambda (x)
       (if (not (equal? (nth x 2) "-"))
           (let* ((r (car x)) (rc (nth x 1)) (sec (au-f rc 4))
                  (same (filter (lambda (y) (equal? (au-f (nth y 1) 4) sec)) structural))
                  (nb (length (filter (lambda (y) (< (nth (car y) 0) (nth r 0))) same)))
                  (na (length (filter (lambda (y) (> (nth (car y) 0) (nth r 0))) same)))
                  (pos (cond ((= (+ nb na) 0) "нет структурных") ((= nb 0) "до всех структурных")
                             ((= na 0) "после всех структурных") (else "между")))
                  (sh (if (and grid? (equal? (nth x 2) "recognizer"))
                          (au2-rec-shadow r (au2-take-n (map car (sort (filter (lambda (y) (> (nth (car y) 0) (nth r 0))) same)
                                                                       (lambda (p q) (< (nth (car p) 0) (nth (car q) 0)))))
                                                         au2-rec-cap))
                          (list "-" "-" '()))))
             (au-tsv-line (list ch sec (nth r 1) (nth r 0) (nth x 2) (au-join (nth x 3) ",") nb na pos
                                (nth sh 0) (nth sh 1)
                                (au-join (map (lambda (b) (substring (nth b 1) 5 (string-length (nth b 1))))
                                              (au2-take-n (nth sh 2) 4)) " "))))))
     recs)))

(define (au2-take-n l n) (if (or (null? l) (= n 0)) '() (cons (car l) (au2-take-n (cdr l) (- n 1)))))

; =====================================================================================================
; RUBI.AUDIT.2 (часть 5): «головные» входы — sec/csc/cot на уровне типа множителя
; =====================================================================================================
; Образцы правил порта записаны степенями cos/sin ((sec u) = (^ (cos u) -1)); вход с головой sec/csc/cot при *rubi-nf* #t
; остаётся головой и правил не находит (разбор потерь главы 4 при единой форме). Проверка на уровне типа: сигнатура входа, в которой
; sec/csc/cot считаются обратными степенями cos/sin/tan, совпадает с листом правила, которое берёт вход при #f?
(define (au2-recip e)
  (cond ((not (pair? e)) e)
        ((and (member? (car e) '(sec csc cot)) (= (length e) 2))
         (list '^ (list (cadr (assoc (car e) '((sec cos) (csc sin) (cot tan)))) (au2-recip (cadr e))) -1))
        ((and (equal? (car e) 'sqrt) (= (length e) 2)) (list '^ (au2-recip (cadr e)) '(/ 1 2)))
        (else (map au2-recip e))))

; полное раскрытие в sin/cos: sec = cos^-1, csc = sin^-1, tan = sin*cos^-1, cot = cos*sin^-1 (и sqrt как степень 1/2)
(define (au2-expand e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'sec) (= (length e) 2)) (list '^ (list 'cos (au2-expand (cadr e))) -1))
        ((and (equal? (car e) 'csc) (= (length e) 2)) (list '^ (list 'sin (au2-expand (cadr e))) -1))
        ((and (equal? (car e) 'tan) (= (length e) 2))
         (list '* (list 'sin (au2-expand (cadr e))) (list '^ (list 'cos (au2-expand (cadr e))) -1)))
        ((and (equal? (car e) 'cot) (= (length e) 2))
         (list '* (list 'cos (au2-expand (cadr e))) (list '^ (list 'sin (au2-expand (cadr e))) -1)))
        ((and (equal? (car e) 'sqrt) (= (length e) 2)) (list '^ (au2-expand (cadr e)) '(/ 1 2)))
        (else (map au2-expand e))))

(define (au2-sqrt e)
  (cond ((not (pair? e)) e)
        ((and (equal? (car e) 'sqrt) (= (length e) 2)) (list '^ (au2-sqrt (cadr e)) '(/ 1 2)))
        (else (map au2-sqrt e))))

(define (au2-has-recip-head? e)
  (cond ((not (pair? e)) #f)
        ((and (member? (car e) '(sec csc cot)) (= (length e) 2)) #t)
        (else (any? au2-has-recip-head? e))))

; правило по id: id -> лист (грубая сигнатура), по записям au-records
(define (au2-leaf-map)
  (let ((m (make-hash)))
    (for-each (lambda (rc) (hash-set! m (au-f rc 0) (au-f rc 5))) (au-records))
    m))

; строка таблицы для задачи «id<TAB>вход»
(define (au2-head-row line leafs)
  (let* ((parts (string-split line "\t")) (id (car parts)) (input (cadr parts))
         (e (try (math-read input) (lambda (err) #f))))
    (if (not e)
        (au-tsv-line (list id input "parse-error" "-" "-" "-" "-" "-" "-" "-" "-" "-"))
        (let* ((ne (try (rubi::rubi-norm-form e) (lambda (err) e)))
               (sp (nth (au-classify (au2-sqrt e)) 0))    ; вход как есть (голова sec/csc/cot остаётся типом)
               (sr (nth (au-classify (au2-recip e)) 0))   ; sec = cos^-1, csc = sin^-1, cot = tan^-1 на уровне типа
               (sx (nth (au-classify (au2-expand e)) 0))  ; всё раскрыто в sin/cos
               (st (rubi::fz-step ne))
               (res (car st))
               (fire (let ((fs (rubi::fz-fires (cadr st)))) (if (pair? fs) (car fs) #f)))
               (fid (if fire (cadr fire) "-"))
               (leaf (if fire (hash-ref leafs fid "-") "-")))
          (au-tsv-line (list id input (if (equal? res 'unknown) "unknown" "answer") fid leaf sp sr sx
                             (if (equal? leaf "-") "-" (if (equal? leaf sp) "yes" "no"))
                             (if (equal? leaf "-") "-" (if (equal? leaf sr) "yes" "no"))
                             (if (equal? leaf "-") "-" (if (equal? leaf sx) "yes" "no"))
                             (if (equal? leaf "-") "-" (if (or (equal? leaf sp) (equal? leaf sr) (equal? leaf sx)) "yes" "no"))))))))

(define (au2-heads-run path)
  (au-rules)
  (au2-ensure-fuzz)
  (set! rubi::*rubi-tries-limit* 6000)
  (let ((leafs (au2-leaf-map)))
    (display "id\tinput\tat_f\tfired_rule\tleaf_of_rule\tsig_plain\tsig_recip\tsig_expand\tleaf_eq_plain\tleaf_eq_recip\tleaf_eq_expand\tleaf_eq_any")
    (newline)
    (for-each (lambda (l) (au2-head-row l leafs))
              (filter (lambda (l) (> (string-length l) 0))
                      (map (lambda (l) (if (and (> (string-length l) 0) (equal? (substring l (- (string-length l) 1) (string-length l)) "\r")) (substring l 0 (- (string-length l) 1)) l))
                           (string-split (read-text-file path) (format "~%")))))))

; ---------- помощники для тестов и отладки ----------
; вложение образцов без правил: привязки A к образцу B с константами вместо переменных, либо #f
(define (au2-pat-contains pa pb)
  (let* ((prep (ac-build-prepared pa))
         (ms (map (lambda (i) (try (ac-match-prepared prep (rubi::rubi-norm-form i) #f) (lambda (e) #f)))
                  (au2-instances pb))))
    (and (every? (lambda (m) m) ms) (car ms))))

(define (au2-rule-by-id id)
  (let ((l (filter (lambda (r) (equal? (nth r 1) id)) (au-rules)))) (if (pair? l) (car l) #f)))

(define (au2-record-by-id id)
  (let ((l (filter (lambda (rc) (equal? (au-f rc 0) id)) (au-records)))) (if (pair? l) (car l) #f)))

; (вид утилиты) узла «распознаватель» правила по id
(define (au2-kind-of-id id) (au2-rec-kind (au2-rule-by-id id) (au2-record-by-id id)))

; (классы предикаты) произвольных переменных правила по id, #f — переменных нет
(define (au2-arb-of-id id) (au2-arb-info (au2-rule-by-id id)))

; анализ пары правил по id: вид условия (dup | cond-entailed | cond-open | cond-false) или #f — вложения нет
(define (au2-pair-of-ids ida idb)
  (let ((res (au2-pair (au2-rule-by-id ida) (au2-rule-by-id idb)))) (and res (car res))))
