// TEX.1: разбор подмножества LaTeX, которое выдаёт LatexPrinter (для кругового теста).
// Возвращает Lisp-форму; неподдерживаемая конструкция — исключение Unsupported.
module LatexParse

open System
open Types

exception Unsupported of string

type private Tok =
    | TNum of string
    | TIdent of string
    | TCmd of string
    | TOp of string
    | TPunct of string
    | TEnd

let private tokenize (s: string) : Tok list =
    let res = ResizeArray<Tok>()
    let mutable i = 0
    let isLetter c = Char.IsLetter c
    let isDigit c = Char.IsDigit c
    while i < s.Length do
        let c = s.[i]
        if c = ' ' || c = '\t' || c = '\n' then i <- i + 1
        elif c = '\\' then
            let j = i + 1
            let mutable k = j
            while k < s.Length && Char.IsLetter s.[k] do k <- k + 1
            let name = s.Substring(j, k - j)
            if name = "left" || name = "right" then
                if k < s.Length then
                    match s.[k] with
                    | '(' | ')' | '[' | ']' -> res.Add(TPunct(string s.[k])); i <- k + 1
                    | '{' -> res.Add(TPunct(if name = "left" then "L{" else "R}")); i <- k + 1
                    | '\\' -> res.Add(TPunct(if name = "left" then "L{" else "R}")); i <- k + 2
                    | _ -> i <- k
                else i <- k
            elif name = "" then
                if k < s.Length then
                    match s.[k] with
                    | ',' | '!' | ';' | ' ' -> i <- k + 1
                    | '\\' -> res.Add(TCmd "row"); i <- k + 1
                    | '{' -> res.Add(TPunct "{"); i <- k + 1
                    | '}' -> res.Add(TPunct "}"); i <- k + 1
                    | '_' -> res.Add(TCmd "_"); i <- k + 1
                    | _ -> i <- k + 1
                else i <- k
            else
                res.Add(TCmd name); i <- k
        elif isDigit c || c = '.' then
            let j = i
            let mutable k = i
            while k < s.Length && (isDigit s.[k] || s.[k] = '.') do k <- k + 1
            res.Add(TNum(s.Substring(j, k - j))); i <- k
        elif isLetter c then
            let j = i
            let mutable k = i
            while k < s.Length && (isLetter s.[k] || isDigit s.[k]) do k <- k + 1
            res.Add(TIdent(s.Substring(j, k - j))); i <- k
        else
            match c with
            | '{' | '}' | '(' | ')' | '[' | ']' | ',' | '&' -> res.Add(TPunct(string c))
            | _ -> res.Add(TOp(string c))
            i <- i + 1
    res.Add TEnd
    List.ofSeq res

let private greekNames =
    Map.ofList [
        "alpha", "alpha"; "beta", "beta"; "gamma", "gamma"; "delta", "delta"; "epsilon", "epsilon"
        "zeta", "zeta"; "eta", "eta"; "theta", "theta"; "iota", "iota"; "kappa", "kappa"; "lambda", "lambda"
        "mu", "mu"; "nu", "nu"; "xi", "xi"; "pi", "pi"; "rho", "rho"; "sigma", "sigma"; "tau", "tau"
        "upsilon", "upsilon"; "phi", "phi"; "chi", "chi"; "psi", "psi"; "omega", "omega"
        "Gamma", "Gamma"; "Delta", "Delta"; "Theta", "Theta"; "Lambda", "Lambda"; "Xi", "Xi"; "Pi", "Pi"
        "Sigma", "Sigma"; "Phi", "Phi"; "Psi", "Psi"; "Omega", "Omega" ]

let private funcNames =
    Map.ofList [
        "sin", "sin"; "cos", "cos"; "tan", "tan"; "cot", "cot"; "sec", "sec"; "csc", "csc"
        "sinh", "sinh"; "cosh", "cosh"; "tanh", "tanh"; "coth", "coth"
        "arcsin", "asin"; "arccos", "acos"; "arctan", "atan"
        "log", "log"; "ln", "ln" ]

let private sfLetter =
    Map.ofList [ "J", "bessel-j"; "Y", "bessel-y"; "I", "bessel-i"; "K", "bessel-k"
                 "P", "legendre-p"; "Q", "legendre-q" ]

let private indexText (v: LispValue) : string =
    match v with
    | LispInteger n -> string n
    | LispRational (p, q) -> string p + "/" + string q
    | LispSym s -> s
    | _ -> "x"

let private num (t: string) : LispValue =
    if t.Contains "." then LispFloat (float t) else LispInteger (bigint.Parse t)

type private P(toks: Tok[]) =
    let mutable i = 0
    member _.Peek = toks.[i]
    member _.Take() = let t = toks.[i] in i <- i + 1; t
    member p.Expect(t: Tok) = if p.Take() <> t then raise (Unsupported("ожидался " + string t))
    member _.Skip() = i <- i + 1
    member p.Is(t: Tok) = (p.Peek = t)

    member p.ParseTop() : LispValue =
        let v = p.ParseOr()
        if not (p.Is TEnd) then raise (Unsupported "остались токены")
        v

    member p.ParseOr() : LispValue =
        let first = p.ParseAnd()
        let rec loop acc =
            match p.Peek with
            | TCmd "lor" -> p.Skip(); loop (acc @ [ p.ParseAnd() ])
            | _ -> acc
        match loop [ first ] with
        | [ one ] -> one
        | many -> LispList(LispSym "or" :: many)

    member p.ParseAnd() : LispValue =
        let first = p.ParseRel()
        let rec loop acc =
            match p.Peek with
            | TCmd "land" -> p.Skip(); loop (acc @ [ p.ParseRel() ])
            | _ -> acc
        match loop [ first ] with
        | [ one ] -> one
        | many -> LispList(LispSym "and" :: many)

    member p.RelOp() : string option =
        match p.Peek with
        | TCmd "ne" -> p.Skip(); Some "!="
        | TCmd "le" -> p.Skip(); Some "<="
        | TCmd "ge" -> p.Skip(); Some ">="
        | TCmd "in" -> p.Skip(); Some ":in"
        | TOp "=" -> p.Skip(); Some "="
        | TOp "<" -> p.Skip(); Some "<"
        | TOp ">" -> p.Skip(); Some ">"
        | _ -> None

    member p.ParseRel() : LispValue =
        match p.Peek with
        | TCmd "lnot" -> p.Skip(); LispList [ LispSym "not"; p.ParseRel() ]
        | _ ->
            let l = p.ParseSum()
            match p.RelOp() with
            | Some op -> LispList [ LispSym op; l; p.ParseSum() ]
            | None -> l

    member p.ParseSum() : LispValue =
        let mutable acc = p.ParseProd()
        let mutable go = true
        while go do
            match p.Peek with
            | TOp "+" -> p.Skip(); acc <- LispList [ LispSym "+"; acc; p.ParseProd() ]
            | TOp "-" -> p.Skip(); acc <- LispList [ LispSym "-"; acc; p.ParseProd() ]
            | _ -> go <- false
        acc

    member p.StartsAtom() =
        match p.Peek with
        | TNum _ | TIdent _ -> true
        | TCmd c -> not (List.contains c [ "cdot"; "lor"; "land"; "le"; "ge"; "ne"; "in"; "to"; "row" ])
        | TPunct "(" | TPunct "L{" | TPunct "[" | TPunct "{" | TPunct "L[" -> true
        | _ -> false

    member p.ParseProd() : LispValue =
        let mutable acc = p.ParseUnary()
        let mutable go = true
        while go do
            match p.Peek with
            | TOp "*" | TCmd "cdot" -> p.Skip(); acc <- LispList [ LispSym "*"; acc; p.ParseUnary() ]
            | TOp "/" -> p.Skip(); acc <- LispList [ LispSym "/"; acc; p.ParseUnary() ]
            | _ when p.StartsAtom() -> acc <- LispList [ LispSym "*"; acc; p.ParseUnary() ]
            | _ -> go <- false
        acc

    member p.ParseUnary() : LispValue =
        match p.Peek with
        | TOp "-" -> p.Skip(); LispList [ LispSym "-"; p.ParseUnary() ]
        | TOp "+" -> p.Skip(); p.ParseUnary()
        | TCmd "lnot" -> p.Skip(); LispList [ LispSym "not"; p.ParseUnary() ]
        | _ -> p.ParsePower()

    member p.ParsePower() : LispValue =
        let b0 = p.ParseAtom()
        let b = if p.Is(TOp "!") then (p.Skip(); LispList [ LispSym "factorial"; b0 ]) else b0
        match p.Peek with
        | TOp "^" -> p.Skip(); LispList [ LispSym "^"; b; p.ParseBraceOrAtom() ]
        | _ -> b

    member p.ParseBraceOrAtom() : LispValue =
        match p.Peek with
        | TPunct "{" | TPunct "L{" ->
            p.Skip()
            let v = p.ParseOr()
            match p.Peek with
            | TPunct "}" | TPunct "R}" -> p.Skip()
            | _ -> raise (Unsupported "закрывающая }")
            v
        | _ -> p.ParseAtom()

    member p.ParseArg() : LispValue =
        match p.Peek with
        | TPunct "(" ->
            p.Skip(); let v = p.ParseOr() in p.Expect(TPunct ")"); v
        | TPunct "{" | TPunct "L{" ->
            p.Skip()
            let v = p.ParseOr()
            match p.Peek with
            | TPunct "}" | TPunct "R}" -> p.Skip()
            | _ -> raise (Unsupported "закрывающая }")
            v
        | _ -> p.ParseAtom()

    member p.Args() : LispValue list =
        if p.Is(TPunct "(") then
            p.Skip()
            let rec many acc =
                let v = p.ParseOr()
                match p.Peek with
                | TPunct "," -> p.Skip(); many (v :: acc)
                | TPunct ")" -> p.Skip(); List.rev (v :: acc)
                | _ -> raise (Unsupported "аргументы")
            many []
        else []

    member p.ParseBigOp(name: string) : LispValue =
        if p.Is(TOp "_") then p.Skip()
        let lo = p.ParseBraceOrAtom()
        let hi = if p.Is(TOp "^") then (p.Skip(); p.ParseBraceOrAtom()) else raise (Unsupported "предел суммы")
        let v, a =
            match lo with
            | LispList [ LispSym "="; LispSym k; a ] -> k, a
            | _ -> raise (Unsupported "нижний предел")
        let body = p.ParseProd()
        LispList [ LispSym name; body; LispSym v; a; hi ]

    member p.ParseAtom() : LispValue =
        match p.Peek with
        | TOp "|" ->
            p.Skip()
            let v = p.ParseOr()
            if not (p.Is(TOp "|")) then raise (Unsupported "|")
            p.Skip()
            LispList [ LispSym "abs"; v ]
        | TCmd "begin" -> p.ParseEnvironment()
        | _ -> p.ParseAtomCore()

    member p.ParseEnvironment() : LispValue =
        p.Expect(TPunct "{")
        let name = match p.Take() with TIdent t -> t | _ -> raise (Unsupported "окружение")
        p.Expect(TPunct "}")
        let rec rows acc =
            let rec cells cs =
                let cell = p.ParseOr()
                if p.Is(TPunct "&") then (p.Skip(); cells (cell :: cs)) else List.rev (cell :: cs)
            let cs = cells []
            match p.Peek with
            | TCmd "row" -> p.Skip(); rows (cs :: acc)
            | _ -> List.rev (cs :: acc)
        let all = rows []
        p.Expect(TCmd "end")
        p.Expect(TPunct "{")
        let _ = p.Take()
        p.Expect(TPunct "}")
        match name with
        | "pmatrix" ->
            LispList(LispSym "m-vector" :: (all |> List.map (fun cs -> LispList(LispSym "m-vector" :: cs))))
        | "cases" ->
            let branches =
                all |> List.map (function
                    | [ e; c ] -> LispList [ c; e ]
                    | _ -> raise (Unsupported "cases"))
            LispList [ LispSym "piecewise"; LispList branches ]
        | _ -> raise (Unsupported ("окружение " + name))

    member p.ParseIntBody() : LispValue =
        let mutable acc = p.ParseUnary()
        let mutable go = true
        while go do
            match p.Peek with
            | TOp "*" | TCmd "cdot" -> p.Skip(); acc <- LispList [ LispSym "*"; acc; p.ParseUnary() ]
            | TOp "/" -> p.Skip(); acc <- LispList [ LispSym "/"; acc; p.ParseUnary() ]
            | TIdent dv when dv.Length = 2 && dv.[0] = 'd' -> go <- false
            | _ when p.StartsAtom() -> acc <- LispList [ LispSym "*"; acc; p.ParseUnary() ]
            | _ -> go <- false
        acc

    member p.ParseAtomCore() : LispValue =
        match p.Take() with
        | TNum t -> num t
        | TIdent "e" ->
            match p.Peek with
            | TOp "^" -> p.Skip(); LispList [ LispSym "exp"; p.ParseBraceOrAtom() ]
            | _ -> LispSym "e"
        | TIdent t ->
            // индекс _: x_{1}, J_{1/3}
            let mutable name = t
            let mutable idx = None
            if p.Is(TOp "_") then
                p.Skip()
                idx <- Some(p.ParseBraceOrAtom())
            match idx, sfLetter.TryFind t with
            | Some iv, Some sf ->
                let args = p.Args()
                match args with
                | [ a ] -> LispList [ LispSym sf; iv; a ]
                | _ -> raise (Unsupported "спецфункция")
            | Some iv, None -> LispSym(name + "_" + indexText iv)
            | None, _ -> LispSym name
        | TPunct "(" ->
            let v = p.ParseOr()
            p.Expect(TPunct ")")
            v
        | TPunct "[" | TPunct "L[" ->
            let close = if p.Peek = TPunct "[" then TPunct "]" else TPunct "]" // \left[ ... \right] — тот же токен
            let rec items acc =
                let v = p.ParseOr()
                match p.Peek with
                | TPunct "," -> p.Skip(); items (v :: acc)
                | TPunct "]" -> p.Skip(); List.rev (v :: acc)
                | _ -> raise (Unsupported "вектор")
            LispList(LispSym "m-vector" :: items [])
        | TPunct "L{" ->
            let rec items acc =
                let v = p.ParseOr()
                match p.Peek with
                | TPunct "," -> p.Skip(); items (v :: acc)
                | TPunct "R}" -> p.Skip(); List.rev (v :: acc)
                | _ -> raise (Unsupported "множество")
            LispList(LispSym "m-set" :: items [])
        | TCmd "infty" -> LispSym "inf"
        | TCmd "Gamma" ->
            let args = p.Args()
            LispList(LispSym "gamma" :: args)
        | TCmd "psi" ->
            let args = p.Args()
            LispList(LispSym "psi" :: args)
        | TCmd g when greekNames.ContainsKey g ->
            let g0 = LispSym greekNames.[g]
            if p.Is(TOp "_") then
                p.Skip()
                let iv = p.ParseBraceOrAtom()
                LispSym((match g0 with LispSym s -> s | _ -> g) + "_" + indexText iv)
            else g0
        | TCmd "gamma" -> LispSym "euler-gamma"
        | TCmd "frac" ->
            let a = p.ParseArg()
            let b = p.ParseArg()
            // \frac{d}{dx} f — невычисленная производная
            match a, b with
            | LispSym "d", LispSym dx when dx.StartsWith "d" && dx.Length = 2 ->
                let f = p.ParseAtom()
                LispList [ LispSym "diff"; f; LispSym(string dx.[1]) ]
            | _ -> LispList [ LispSym "/"; a; b ]
        | TCmd "sqrt" ->
            match p.Peek with
            | TPunct "[" ->
                p.Skip()
                let d = p.ParseOr()
                p.Expect(TPunct "]")
                let a = p.ParseArg()
                LispList [ LispSym "^"; a; LispList [ LispSym "/"; LispInteger 1I; d ] ]
            | _ -> LispList [ LispSym "^"; p.ParseArg(); LispRational (1I, 2I) ]
        | TCmd "binom" ->
            let a = p.ParseArg()
            let b = p.ParseArg()
            LispList [ LispSym "binomial"; a; b ]
        | TCmd "operatorname" ->
            p.Expect(TPunct "{")
            let sb = Text.StringBuilder()
            let mutable go = true
            while go do
                match p.Take() with
                | TIdent t -> sb.Append(t) |> ignore
                | TOp "-" | TCmd "textasciicircum" -> sb.Append('-') |> ignore
                | TCmd "_" -> sb.Append('_') |> ignore
                | TPunct "}" -> go <- false
                | other -> raise (Unsupported("operatorname: " + string other))
            let name = sb.ToString()
            let args = p.Args()
            let name = if name = "Ai" then "airy-ai" elif name = "Bi" then "airy-bi" else name
            LispList(LispSym name :: args)
        | TCmd "int" ->
            let lo = if p.Is(TOp "_") then (p.Skip(); Some(p.ParseBraceOrAtom())) else None
            let hi = if p.Is(TOp "^") then (p.Skip(); Some(p.ParseBraceOrAtom())) else None
            let e = p.ParseIntBody()
            match p.Peek with
            | TIdent dv when dv.Length = 2 && dv.[0] = 'd' ->
                p.Skip()
                match lo, hi with
                | Some a, Some b -> LispList [ LispSym "integrate"; e; LispSym(string dv.[1]); a; b ]
                | _ -> LispList [ LispSym "integrate"; e; LispSym(string dv.[1]) ]
            | _ -> raise (Unsupported "интеграл без dx")
        | TCmd "sum" -> p.ParseBigOp "sum"
        | TCmd "prod" -> p.ParseBigOp "product"
        | TCmd "lim" ->
            if p.Is(TOp "_") then p.Skip()
            if not (p.Is(TPunct "{")) then raise (Unsupported "lim")
            p.Skip()
            let x = p.ParseAtom()
            match p.Peek with
            | TCmd "to" -> p.Skip()
            | _ -> raise (Unsupported "lim: to")
            let a = p.ParseOr()
            p.Expect(TPunct "}")
            let body = p.ParseProd()
            LispList [ LispSym "limit"; body; x; a ]
        | TCmd c when funcNames.ContainsKey c ->
            let name = funcNames.[c]
            let mutable pw = None
            if p.Is(TOp "^") then
                p.Skip()
                pw <- Some(p.ParseBraceOrAtom())
            let arg = p.ParseArg()
            let basev = LispList [ LispSym name; arg ]
            match pw with
            | Some e -> LispList [ LispSym "^"; basev; e ]
            | None -> basev
        | other -> raise (Unsupported("токен " + string other))

let parse (s: string) : LispValue =
    let toks = tokenize s |> List.toArray
    P(toks).ParseTop()
