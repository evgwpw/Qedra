// Шаг MATCH.FS: ядро AC-сопоставителя на F# (AcMatchBuiltins) — builtin-ы и совпадение с Lisp-эталоном (match::*ac-native* #f)
module AcMatchTests

open Xunit
open Types
open Reader
open Evaluator
open Builtins

let evalStr (s: string) : LispValue = readAll s |> List.head |> fun e -> eval e globalEnv

let private show (s: string) = Printer.prettyPrint (evalStr s)

[<Fact>]
let ``MATCH.FS: ac-native-ok? — образец с головой-переменной F#-ядру не годится`` () =
    Assert.Equal("(#t #t)", show "(list (ac-native-ok? (cadr (ac-build-prepared '(+ ?a (* ?b x))))) (ac-native-ok? (cadr (ac-build-prepared '(^ ?x ?n)))))")
    Assert.Equal("#f", show "(ac-native-ok? '(NV (V ?f #f) ((V ?x #f))))")

[<Fact>]
let ``MATCH.FS: ac-search-native — решения, счётчик и лимит в ctx`` () =
    // два решения (?a ?b) в сумме трёх слагаемых; callback #f — перебор идёт дальше, счётчик пишется в ctx
    let r = show "(let* ((ip (cadr (ac-build-prepared '(+ ?a ?b ?r...)))) (ctx (vector 0 10000 #f #f #f)) (sols '())) (ac-search-native ip '(+ x y z) ctx (lambda (b) (set! sols (cons b sols)) #f) #f) (list (length sols) (> (vref ctx 0) 0) (vref ctx 2)))"
    Assert.Equal("(6 #t #f)", r)
    // лимит 3: превышение — флаг в ctx, результат #f
    let r2 = show "(let* ((ip (cadr (ac-build-prepared '(+ ?a ?b ?r...)))) (ctx (vector 0 3 #f #f #f))) (list (ac-search-native ip '(+ x y z) ctx (lambda (b) #f) #f) (vref ctx 2)))"
    Assert.Equal("(#f #t)", r2)

[<Fact>]
let ``MATCH.FS: Lisp-путь и F#-путь дают одинаковые решения в том же порядке`` () =
    let script =
        "(let ((cases '(((+ ?a (* ?b x)) (+ 3 (* 5 x)))
                        ((* ?a ?b) (* 2 x y))
                        ((* ?a (^ (+ ?b ?c) ?p)) (* (+ x 1) (^ (+ x 2) 3)))
                        ((^ ?x ?n) y)
                        ((+ (sin ?u) (cos ?u) ?r...) (+ (sin x) (cos x) 4 z))
                        ((* ?a ?a) (* x x))
                        ((+ ?a ?b) (+ x y z)))))
           (let ((one (lambda (flag)
                        (set! match::*ac-native* flag)
                        (map (lambda (c) (list (ac-match-all (car c) (cadr c))
                                               (ac-match-all (car c) (cadr c) :identities #t)
                                               (ac-match (car c) (cadr c))
                                               (ac-match-all (car c) (cadr c) 4)))
                             cases))))
             (let ((a (one #f)) (b (one #t)))
               (set! match::*ac-native* #t)
               (equal? a b))))"
    Assert.Equal("#t", show script)
