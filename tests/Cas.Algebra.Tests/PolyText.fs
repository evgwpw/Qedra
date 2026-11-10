// Вспомогательное для тестов алгебры: многочлены MPoly из инфиксной записи ("(x-1)*(x+2)^2*(a*t+1)", "1/2*x + 3").
// Типов Lisp нет: имена переменных ставятся в соответствие номерам MPoly явно (VarCtx).
// Порядок номеров — как у PolyExpr.makeCtx (Lisp.Core): «главные» переменные (mains) — наибольшие номера в указанном порядке;
// остальные имена — по убыванию (алфавитно ПЕРВОЕ имя получает наибольший из оставшихся номеров).
module PolyText

open System
open System.Numerics
open System.Text.RegularExpressions
open MPoly

type VarCtx = { Names: string[] }

let private identsOf (s: string) : string list =
    [ for m in Regex.Matches(s, "[A-Za-z_][A-Za-z_0-9]*") -> m.Value ]

// srcs — тексты, из которых берутся имена переменных; mains — имена с наибольшими номерами (в этом порядке)
let ctxOf (srcs: string list) (mains: string list) : VarCtx =
    let all = srcs |> List.collect identsOf |> List.distinct
    let rest =
        all |> List.filter (fun n -> not (List.contains n mains))
            |> List.sortWith (fun a b -> String.CompareOrdinal(b, a))
    { Names = Array.ofList (rest @ mains) }

let idx (ctx: VarCtx) (name: string) : int =
    match Array.tryFindIndex ((=) name) ctx.Names with
    | Some i -> i
    | None -> failwithf "нет переменной %s" name

// --- разбор: expr := term (('+' | '-') term)*;  term := unary (('*' | '/') unary)*;  unary := '-' unary | power;
//     power := atom ('^' целое)?;  atom := целое | имя | '(' expr ')'.  Деление — только на числовую константу.
type private Parser(ctx: VarCtx, text: string) =
    let mutable pos = 0
    member private _.Skip() = while pos < text.Length && Char.IsWhiteSpace text.[pos] do pos <- pos + 1
    member private p.Peek() : char =
        p.Skip()
        if pos < text.Length then text.[pos] else '\000'
    member private p.Eat(c: char) : bool =
        if p.Peek() = c then
            pos <- pos + 1
            true
        else false
    member p.Expr() : MPoly =
        let mutable acc = p.Term()
        let mutable go = true
        while go do
            if p.Eat '+' then acc <- add acc (p.Term())
            elif p.Eat '-' then acc <- sub acc (p.Term())
            else go <- false
        acc
    member p.Term() : MPoly =
        let mutable acc = p.Unary()
        let mutable go = true
        while go do
            if p.Eat '*' then acc <- mul acc (p.Unary())
            elif p.Eat '/' then
                match p.Unary() with
                | Const (n, d) when not n.IsZero -> acc <- mulConst (d, n) acc
                | _ -> failwithf "деление не на число: %s" text
            else go <- false
        acc
    member p.Unary() : MPoly = if p.Eat '-' then neg (p.Unary()) else p.Power()
    member p.Power() : MPoly =
        let a = p.Atom()
        if p.Eat '^' then
            match p.Atom() with
            | Const (n, d) when d.IsOne -> pow a (int n)
            | _ -> failwithf "показатель — не целое: %s" text
        else a
    member p.Atom() : MPoly =
        let c = p.Peek()
        if c = '(' then
            pos <- pos + 1
            let e = p.Expr()
            if not (p.Eat ')') then failwithf "нет ): %s" text
            e
        elif Char.IsDigit c then
            let start = pos
            while pos < text.Length && Char.IsDigit text.[pos] do pos <- pos + 1
            ofInt (BigInteger.Parse (text.Substring(start, pos - start)))
        elif Char.IsLetter c || c = '_' then
            let start = pos
            while pos < text.Length && (Char.IsLetterOrDigit text.[pos] || text.[pos] = '_') do pos <- pos + 1
            var (idx ctx (text.Substring(start, pos - start)))
        else failwithf "неожиданный символ '%c' в %s" c text
    member p.Done() : bool = p.Peek() = '\000'

let polyIn (ctx: VarCtx) (text: string) : MPoly =
    let p = Parser(ctx, text)
    let r = p.Expr()
    if not (p.Done()) then failwithf "лишний текст в %s" text
    r

// Для сообщений об ошибках: многочлен как сумма мономов «c*x^k*y^m»
let show (ctx: VarCtx) (p: MPoly) : string =
    if isZero p then "0"
    else
        monomials p
        |> List.map (fun ((n, d), ms) ->
            let c = if d.IsOne then string n else sprintf "%A/%A" n d
            let vs = ms |> List.rev |> List.map (fun (v, k) -> if k = 1 then ctx.Names.[v] else sprintf "%s^%d" ctx.Names.[v] k)
            String.Join("*", c :: vs))
        |> String.concat " + "
