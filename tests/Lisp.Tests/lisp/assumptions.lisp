; assumptions.lisp — тесты шага AS: допущения и ветви sqrt/log (refine, assuming, branch_check).
; Оракулы: главная ветвь (arg ∈ (−π, π]): √(x²) = x (x>0), −x (x<0), |x| (x вещественный); log(x²) = 2 log x (x>0),
; 2 log(−x) (x<0); log(ab) = log a + log b при a > 0; log(exp t) = t для вещественного t.
; Подделки: тождества без допущений (log(ab) = log a + log b, √(x²) = x при x < 0) — mismatch (точки a = b = −1).
; Без допущений ответы не меняются.

(define (asm s) (math-eval s))

(deftest "as: refine sqrt(x^2) по знаку x"
  (assert-equal (asm "refine(sqrt(x^2), x > 0)") 'x)
  (assert-equal (asm "refine(sqrt(x^2), x < 0)") '(* -1 x))
  (assert-equal (asm "refine(sqrt(x^2), x in reals)") '(abs x))
  (assert-equal (asm "refine((x^2)^(1/2), x >= 0)") 'x)
  (assert-equal (asm "assuming(x < 0, sqrt(x^2))") '(* -1 x)))

(deftest "as: refine log(x^n) и log(произведения)"
  (assert-equal (asm "refine(log(x^2), x > 0)") '(* 2 (log x)))
  (assert-equal (asm "refine(log(x^2), x < 0)") '(* 2 (log (* -1 x))))
  (assert-equal (asm "refine(log(x^(2*k)), x < 0 and k in integers)") '(* 2 k (log (* -1 x))))
  (assert-equal (asm "refine(log(a*b), a > 0)") '(+ (log a) (log b)))
  (assert-equal (asm "refine(log(a/b), [a > 0, b > 0])") '(+ (log a) (* -1 (log b))))
  (assert-equal (asm "refine(log(exp(t)), t in reals)") 't))

(deftest "as: refine sqrt(a*b) и условия-список"
  (assert-equal (asm "refine(sqrt(a*b), [a > 0])") '(* (sqrt a) (sqrt b)))
  (assert-equal (asm "refine(abs(x), x < 0)") '(* -1 x))
  (assert-equal (asm "refine(abs(x), x > 0 and x < 5)") 'x))

(deftest "as: без допущений ответы не меняются"
  (assert-equal (asm "log(a*b)") '(log (* a b)))
  (assert-equal (asm "log(x^2)") '(log (^ x 2)))
  (assert-equal (asm "log(2*x)") '(log (* 2 x)))
  (assert-equal (asm "sqrt(x^2)") '(sqrt (^ x 2)))
  (assert-equal (asm "refine(log(a*b), a != 0)") '(log (* a b)))
  (assert-equal (asm "refine(log(x^2), x > a)") '(log (^ x 2))))

(deftest "as: декларации не протекают после refine"
  (asm "refine(log(x^2), x > 0)")
  (assert-equal (declarations 'x) '())
  (assert-equal (asm "log(x^2)") '(log (^ x 2))))

(deftest "as: assuming с integrate и simplify"
  (assert-equal (asm "assuming(x > 0, integrate(1/x, x))") '(log x))
  (assert-equal (asm "assuming(x > 0, simplify(log(x^3) - 3*log(x)))") 0))

(deftest "as: branch_check — тождества и подделки"
  (assert-equal (branch-check '(log (* a b)) '(+ (log a) (log b)) #f) 'mismatch)
  (assert-equal (branch-check '(log (* a b)) '(+ (log a) (log b)) '(> a 0)) 'numeric)
  (assert-equal (branch-check '(log (* a b)) '(+ (log a) (log b)) '((> a 0) (> b 0))) 'numeric)
  (assert-equal (branch-check '(sqrt (^ x 2)) 'x '(< x 0)) 'mismatch)
  (assert-equal (branch-check '(sqrt (^ x 2)) '(* -1 x) '(< x 0)) 'numeric)
  (assert-equal (branch-check '(sqrt (^ x 2)) 'x '(> x 0)) 'numeric)
  (assert-equal (branch-check '(log (^ x 2)) '(* 2 (log x)) '(< x 0)) 'mismatch)
  (assert-equal (branch-check '(log (^ x 2)) '(* 2 (log (* -1 x))) '(< x 0)) 'numeric)
  (assert-equal (branch-check '(log (^ x 2)) '(* 2 (log x)) #f) 'mismatch)
  (assert-equal (branch-check '(log (exp t)) 't '(in t reals)) 'numeric)
  (assert-equal (branch-check '(log (exp t)) 't #f) 'mismatch)
  (assert-equal (branch-check '(sqrt (* a b)) '(* (sqrt a) (sqrt b)) '(>= a 0)) 'numeric)
  (assert-equal (branch-check '(sqrt (* a b)) '(* (sqrt a) (sqrt b)) #f) 'mismatch)
  (assert-equal (branch-check '(^ (^ x a) b) '(^ x (* a b)) '((> x 0) (in a reals) (in b reals))) 'numeric)
  (assert-equal (branch-check '(log x) '(log x) '(> x a)) 'unknown))

(deftest "as: branch_check во входном языке и правила — численная сверка"
  (assert-equal (asm "branch_check(log(a*b), log(a)+log(b))") 'mismatch)
  (assert-equal (asm "branch_check(sqrt(x^2), x, x < 0)") 'mismatch)
  (assert-equal (asm "branch_check(log(x^2), 2*log(-x), x < 0)") 'numeric)
  (assert-equal (asm "branch_check(x^2 - 1, (x-1)*(x+1))") 'numeric))

(deftest "as: главная ветвь — численные значения"
  (assert-equal (asm "sqrt(-4)") '(* 2 %i))
  (assert-equal (branch-check '(log -1) '(* %i pi) #f) 'numeric)
  (assert-equal (branch-check '(sqrt -4) '(* 2 %i) #f) 'numeric))
