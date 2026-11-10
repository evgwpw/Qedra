// Индекс кода lib\ («Roslyn для нашего Lisp», Lisp.exe --query): определения, модули, ссылки, запросы.
// Чтение — Checker.parseSource (позиции); код не выполняется. Индекс строится в памяти (файлы не пишутся).
module CodeIndex

open System
open System.Collections.Generic
open System.Text
open System.Text.RegularExpressions
open Checker

type DefKind =
    | KFn
    | KVar
    | KMacro
    | KRule
    | KMethod
    | KType

let kindName (k: DefKind) =
    match k with
    | KFn -> "fn"
    | KVar -> "var"
    | KMacro -> "macro"
    | KRule -> "rule"
    | KMethod -> "method"
    | KType -> "type"

[<AllowNullLiteral>]
type FileInfo(rel: string, lines: string[], isExtra: bool) =
    member _.Rel = rel
    member _.Lines = lines
    member _.IsExtra = isExtra
    member val Module = "" with get, set

[<AllowNullLiteral>]
type Def(name: string, kind: DefKind, modul: string, prms: string list, sg: string, file: FileInfo, line: int, col: int,
         endLine: int, doc: string list, docStart: int) =
    member _.Name = name
    member _.Kind = kind
    member _.Module = modul
    member _.Params = prms
    member _.Sig = sg
    member _.File = file
    member _.Line = line
    member _.Col = col
    member _.EndLine = endLine
    member _.Doc = doc
    member _.DocStart = docStart
    member val Exported = false with get, set

type Ref =
    { Name: string                 // имя без квалификатора
      Qual: string                 // модуль из «модуль::имя» или null
      File: FileInfo
      Line: int
      Col: int
      Quoted: bool                 // 'имя
      Owner: Def                   // объемлющее определение (null — верхний уровень)
      Label: string
      mutable Targets: Def list }

type ModInfo() =
    member val Exports = List<string>() with get
    member val ExportSet = HashSet<string>() with get
    member val Files = List<FileInfo>() with get

type Index(root: string, files: List<FileInfo>, defs: List<Def>, refs: List<Ref>, modules: Dictionary<string, ModInfo>) =
    let byName = Dictionary<string, List<Def>>()
    let refsByName = Dictionary<string, List<Ref>>()
    let refsByOwner = Dictionary<Def, List<Ref>>(HashIdentity.Reference)
    do
        for d in defs do
            if not (byName.ContainsKey d.Name) then byName.[d.Name] <- List<Def>()
            byName.[d.Name].Add d
        for r in refs do
            if not (refsByName.ContainsKey r.Name) then refsByName.[r.Name] <- List<Ref>()
            refsByName.[r.Name].Add r
            if not (isNull r.Owner) then
                if not (refsByOwner.ContainsKey r.Owner) then refsByOwner.[r.Owner] <- List<Ref>()
                refsByOwner.[r.Owner].Add r
    member _.Root = root
    member _.Files = files
    member _.Defs = defs
    member _.Refs = refs
    member _.Modules = modules
    member _.ByName = byName
    member _.RefsByName = refsByName
    member _.RefsByOwner = refsByOwner
    // признак встроенной (F#) функции и список таких имён — задаёт хост (Lisp.Core не знает глобального окружения)
    member val IsBuiltin : string -> bool = (fun _ -> false) with get, set
    member val BuiltinNames : unit -> seq<string> = (fun () -> Seq.empty) with get, set
    // кэш корпуса текстового поиска (строится при первом search)
    member val SearchCache : obj = null with get, set

// ---------- построение ----------

let private isSep (t: string) = Regex.IsMatch(t, @"^;+\s*[-=─*]{3,}")
let private strip (s: string) = s.TrimStart().TrimStart(';').Trim()

// непрерывные строки «;» непосредственно над определением
let private docAbove (lines: string[]) (line: int) : string list * int =
    let acc = List<string>()
    let mutable i = line - 2
    while i >= 0 && lines.[i].TrimStart().StartsWith ";" && not (isSep (lines.[i].TrimStart())) do
        acc.Insert(0, strip lines.[i])
        i <- i - 1
    List.ofSeq acc, (if acc.Count > 0 then i + 2 else line)

// первая группа комментариев внутри определения (сразу после строки заголовка)
let private docInside (lines: string[]) (line: int) (endLine: int) : string list =
    let acc = List<string>()
    let mutable i = line
    while i < endLine && i < lines.Length && lines.[i].TrimStart().StartsWith ";" do
        acc.Add(strip lines.[i])
        i <- i + 1
    List.ofSeq acc

let private paramName (n: Node) = match n with Sym (s, _) -> s | _ -> "?"

let private sigOf (name: string) (ps: string list) =
    if ps.IsEmpty then sprintf "(%s)" name else sprintf "(%s %s)" name (String.Join(" ", ps))

let private paramScope (ps: Node list) =
    ps |> List.choose (function Sym (s, _) when s <> "&rest" -> Some s | _ -> None) |> Set.ofList

let rec private definedNames (forms: Node list) : string list =
    forms |> List.collect (fun f ->
        match f with
        | Lst (Sym ("define", _) :: Sym (n, _) :: _, _, _)
        | Lst (Sym ("define", _) :: Lst (Sym (n, _) :: _, _, _) :: _, _, _)
        | Lst (Sym ("defmemo", _) :: Lst (Sym (n, _) :: _, _, _) :: _, _, _) -> [ n ]
        | Lst (Sym ("begin", _) :: inner, _, _) -> definedNames inner
        | _ -> [])

// Обход выражения: каждая ссылка на символ вне локальной области видимости -> add имя позиция quoted
let rec private walkRefs (add: string -> P -> bool -> unit) (sc: Set<string>) (n: Node) : unit =
    let body (sc2: Set<string>) (forms: Node list) =
        let sc3 = Set.union sc2 (Set.ofList (definedNames forms))
        for f in forms do walkRefs add sc3 f
    match n with
    | Sym (s, p) ->
        if not (Set.contains s sc) && s <> "else" && s <> "&rest" && s <> "." && not (s.Length > 1 && (s.[0] = ':' || s.[0] = '?')) then
            add s p false
    | Lst ([ Sym ("quote", _); Sym (s, p) ], _, _) ->
        if not (s.Length > 1 && s.[0] = ':') then add s p true
    | Lst (Sym ("quote", _) :: _, _, _) -> ()
    | Lst (Sym ("lambda", _) :: Lst (ps, _, _) :: rest, _, _) -> body (Set.union sc (paramScope ps)) rest
    | Lst (Sym (("define" | "defmacro" | "defmemo"), _) :: Lst (_ :: ps, _, _) :: rest, _, _) ->
        body (Set.union sc (paramScope ps)) rest
    | Lst (Sym ("define", _) :: Sym _ :: rest, _, _) -> for f in rest do walkRefs add sc f
    | Lst (Sym (("let" | "let*" | "letrec"), _) :: Sym (loop, _) :: Lst (bs, _, _) :: rest, _, _) ->
        let names = bs |> List.choose (function Lst ([ Sym (s, _); _ ], _, _) -> Some s | _ -> None)
        let sc2 = Set.union (Set.add loop sc) (Set.ofList names)
        for b in bs do
            match b with
            | Lst ([ Sym _; e ], _, _) -> walkRefs add sc2 e
            | other -> walkRefs add sc2 other
        body sc2 rest
    | Lst (Sym (("let" | "let*" | "letrec"), _) :: Lst (bs, _, _) :: rest, _, _) ->
        let names = bs |> List.choose (function Lst ([ Sym (s, _); _ ], _, _) -> Some s | _ -> None)
        let sc2 = Set.union sc (Set.ofList names)
        for b in bs do
            match b with
            | Lst ([ Sym _; e ], _, _) -> walkRefs add sc2 e
            | other -> walkRefs add sc2 other
        body sc2 rest
    | Lst (Sym ("do", _) :: Lst (vars, _, _) :: rest, _, _) ->
        let names = vars |> List.choose (function Lst (Sym (s, _) :: _, _, _) -> Some s | _ -> None)
        let sc2 = Set.union sc (Set.ofList names)
        for v in vars do
            match v with
            | Lst (_ :: more, _, _) -> for m in more do walkRefs add sc2 m
            | _ -> ()
        body sc2 rest
    | Lst (items, _, _) -> for i in items do walkRefs add sc i
    | Vec (items, _) -> for i in items do walkRefs add sc i
    | _ -> ()

let private moduleHeaderOf (forms: Node list) : (string * string list) option =
    match forms with
    | Lst (Sym ("module", _) :: Sym (name, _) :: opts, _, _) :: _ ->
        let exports =
            opts |> List.collect (fun o ->
                match o with
                | Lst (Sym ("export", _) :: names, _, _) -> names |> List.choose (function Sym (s, _) -> Some s | _ -> None)
                | _ -> [])
        Some (name, exports)
    | _ -> None

let private cleanPath (p: string) = p.Replace('\\', '/')

// root — корень репозитория (для относительных имён файлов); files — (полный путь, дополнительный ли файл)
let build (root: string) (files: (string * bool) list) : Index =
    let fileList = List<FileInfo>()
    let defs = List<Def>()
    let refs = List<Ref>()
    let modules = Dictionary<string, ModInfo>()
    let rootFull = (try IO.Path.GetFullPath root with _ -> root)
    let rel (full: string) =
        let f = cleanPath (try IO.Path.GetFullPath full with _ -> full)
        let r = cleanPath rootFull
        let r2 = if r.EndsWith "/" then r else r + "/"
        if f.StartsWith(r2, StringComparison.OrdinalIgnoreCase) then f.Substring r2.Length else f
    for (full, isExtra) in files do
        let text = IO.File.ReadAllText full
        let lines = text.Replace("\r\n", "\n").Split('\n')
        let forms, _ = parseSource full text
        let fi = FileInfo(rel full, lines, isExtra)
        fileList.Add fi
        let modName, exports =
            match moduleHeaderOf forms with
            | Some (m, ex) -> m, ex
            | None -> "", []
        fi.Module <- modName
        if modName <> "" then
            if not (modules.ContainsKey modName) then modules.[modName] <- ModInfo()
            let mi = modules.[modName]
            mi.Files.Add fi
            for e in exports do if mi.ExportSet.Add e then mi.Exports.Add e
        let addDef (name: string) kind (ps: string list) (sg: string) (p: P) (pe: P) : Def =
            let doc0, docStart = docAbove lines p.L
            let doc = if doc0.IsEmpty then docInside lines p.L pe.L else doc0
            let d = Def(name, kind, modName, ps, sg, fi, p.L, p.C, pe.L, doc, docStart)
            defs.Add d
            d
        let walkWith (owner: Def) (label: string) (sc: Set<string>) (nodes: Node list) =
            let add (s: string) (p: P) (q: bool) =
                let qual, nm =
                    match s.IndexOf "::" with
                    | k when k > 0 && k + 2 < s.Length -> s.Substring(0, k), s.Substring(k + 2)
                    | _ -> null, s
                refs.Add { Name = nm; Qual = qual; File = fi; Line = p.L; Col = p.C; Quoted = q; Owner = owner
                           Label = label; Targets = [] }
            let sc2 = Set.union sc (Set.ofList (definedNames nodes))
            for n in nodes do walkRefs add sc2 n
        let rec go (f: Node) =
            match f with
            | Lst (Sym ("begin", _) :: inner, _, _) -> List.iter go inner
            | Lst (Sym ((("define" | "defmemo") as hd), _) :: Lst (Sym (n, _) :: ps, _, _) :: body, p, pe) ->
                let pn = ps |> List.map paramName
                let d = addDef n KFn pn (sigOf n pn) p pe
                walkWith d n (paramScope ps) body
            | Lst (Sym ("defmacro", _) :: Lst (Sym (n, _) :: ps, _, _) :: body, p, pe) ->
                let pn = ps |> List.map paramName
                let d = addDef n KMacro pn (sigOf n pn) p pe
                walkWith d n (paramScope ps) body
            | Lst (Sym ("define", _) :: Sym (n, _) :: [ Lst (Sym ("lambda", _) :: Lst (ps, _, _) :: body, _, _) ], p, pe) ->
                let pn = ps |> List.map paramName
                let d = addDef n KFn pn (sigOf n pn) p pe
                walkWith d n (paramScope ps) body
            | Lst (Sym ("define", _) :: Sym (n, _) :: rest, p, pe) ->
                let d = addDef n KVar [] n p pe
                walkWith d n Set.empty rest
            | Lst (Sym ("defrule", _) :: Sym (n, _) :: pat :: rep :: tail, p, pe) ->
                let d = addDef n KRule [] (sprintf "(defrule %s)" n) p pe
                walkWith d n Set.empty (pat :: rep :: tail)
            | Lst (Sym ("defmethod", _) :: Sym (op, _) :: Lst (tys, _, _) :: Lst (ps, _, _) :: body, p, pe) ->
                let pn = ps |> List.map paramName
                let tn = tys |> List.map paramName
                let sg = sprintf "%s [%s]" (sigOf op pn) (String.Join(" ", tn))
                let d = addDef op KMethod pn sg p pe
                walkWith d op (paramScope ps) body
            | Lst (Sym ("deftype", _) :: tn :: rest, p, pe) ->
                let n =
                    match tn with
                    | Lst ([ Sym ("quote", _); Sym (s, _) ], _, _) | Sym (s, _) -> s
                    | _ -> "?"
                let parent =
                    match rest with
                    | Lst ([ Sym ("quote", _); Sym (s, _) ], _, _) :: _ | Sym (s, _) :: _ -> " " + s
                    | _ -> ""
                addDef n KType [] (sprintf "(deftype %s%s)" n parent) p pe |> ignore
            | Lst (Sym ("deftest", _) :: Str (nm, _) :: body, _, _) ->
                walkWith null (sprintf "deftest \"%s\"" nm) Set.empty body
            | Lst (Sym ("module", _) :: _, _, _) -> ()
            | other -> walkWith null "<верхний уровень>" Set.empty [ other ]
        List.iter go forms
    // экспорт
    for d in defs do
        if d.Module <> "" then d.Exported <- modules.[d.Module].ExportSet.Contains d.Name
    let idx = Index(rootFull, fileList, defs, refs, modules)
    // разрешение ссылок: свой модуль -> экспорт -> (для «глобальных» файлов) ничего
    for r in refs do
        match idx.ByName.TryGetValue r.Name with
        | true, cands ->
            let fm = r.File.Module
            let targets =
                if not (isNull r.Qual) then cands |> Seq.filter (fun d -> d.Module = r.Qual) |> List.ofSeq
                else
                    let same = cands |> Seq.filter (fun d -> d.Module = fm) |> List.ofSeq
                    if not same.IsEmpty then same
                    else cands |> Seq.filter (fun d -> d.Exported) |> List.ofSeq
            r.Targets <- targets
        | _ -> ()
    idx

// ---------- поиск корня и кэш ----------

let findRoot () : string option =
    let rec up (d: IO.DirectoryInfo) =
        if isNull d then None
        elif IO.Directory.Exists(IO.Path.Combine(d.FullName, "lib")) && IO.File.Exists(IO.Path.Combine(d.FullName, "Lisp.slnx")) then
            Some d.FullName
        else up d.Parent
    match up (IO.DirectoryInfo(IO.Directory.GetCurrentDirectory())) with
    | Some r -> Some r
    | None ->
        match up (IO.DirectoryInfo(AppContext.BaseDirectory)) with
        | Some r -> Some r
        | None ->
            if IO.Directory.Exists(IO.Path.Combine(AppContext.BaseDirectory, "lib")) then Some AppContext.BaseDirectory else None

let private cache = Dictionary<string, int64 * Index>()
let private cacheLock = obj ()

// Индекс lib\ (+ тесты/примеры/bench как «дополнительные» — только для ссылок) + заданные файлы. Кэш в памяти по mtime.
let getIndex (rootOpt: string option) (extraFiles: string list) (withTests: bool) : Index =
    lock cacheLock (fun () ->
        let root = match rootOpt with Some r -> r | None -> (match findRoot () with Some r -> r | None -> ".")
        let libFiles =
            let d = IO.Path.Combine(root, "lib")
            if IO.Directory.Exists d then IO.Directory.GetFiles(d, "*.lisp", IO.SearchOption.AllDirectories) |> Array.sort else [||]
        let extras =
          if not withTests then [] else
            [ for sub, pat, deep in [ "tests/Lisp.Tests/lisp", "*.lisp", false; "examples", "*.lisp", true; "bench", "*.lisp", false ] do
                let d = IO.Path.Combine(root, sub)
                if IO.Directory.Exists d then
                    yield! IO.Directory.GetFiles(d, pat, (if deep then IO.SearchOption.AllDirectories else IO.SearchOption.TopDirectoryOnly)) |> Array.sort ]
        let given =
            extraFiles |> List.map (fun f -> IO.Path.GetFullPath f)
            |> List.filter (fun f -> IO.File.Exists f && not (Array.contains f libFiles) && not (List.contains f extras))
        let all = [ for f in libFiles -> f, false ] @ [ for f in extras @ given -> f, true ]
        let key = root + "|" + string withTests + "|" + String.Join("|", given)
        let sigv = all |> List.sumBy (fun (f, _) -> IO.File.GetLastWriteTimeUtc(f).Ticks / 1000L + int64 f.Length)
        match cache.TryGetValue key with
        | true, (s, idx) when s = sigv -> idx
        | _ ->
            let idx = build root all
            cache.[key] <- (sigv, idx)
            idx)

// ---------- справочник builtin из docs\lisp-library-guide.md ----------

let private guideCache = Dictionary<string, Dictionary<string, string * string>>()

let private guideFor (root: string) : Dictionary<string, string * string> =
    lock guideCache (fun () ->
        match guideCache.TryGetValue root with
        | true, g -> g
        | _ ->
            let g = Dictionary<string, string * string>()
            let path = IO.Path.Combine(root, "docs", "lisp-library-guide.md")
            if IO.File.Exists path then
                for line in IO.File.ReadAllLines path do
                    if line.StartsWith "| `(" then
                        let cells = line.Split([| " | " |], StringSplitOptions.None)
                        if cells.Length >= 2 then
                            let desc = cells.[1].Trim().TrimEnd('|').Trim()
                            for m in Regex.Matches(cells.[0], @"`(\([^`]*\))`") do
                                let sg = m.Groups.[1].Value
                                let name = Regex.Match(sg, @"^\(([^\s()]+)").Groups.[1].Value
                                if name <> "" && not (g.ContainsKey name) then g.[name] <- (sg, desc)
            guideCache.[root] <- g
            g)

// ---------- JSON ----------

type J =
    | JS of string
    | JI of int
    | JB of bool
    | JA of J list
    | JO of (string * J) list

let rec private jwrite (sb: StringBuilder) (j: J) =
    match j with
    | JS s ->
        sb.Append '"' |> ignore
        for ch in s do
            match ch with
            | '"' -> sb.Append "\\\"" |> ignore
            | '\\' -> sb.Append "\\\\" |> ignore
            | '\n' -> sb.Append "\\n" |> ignore
            | '\r' -> sb.Append "\\r" |> ignore
            | '\t' -> sb.Append "\\t" |> ignore
            | c when c < ' ' -> sb.AppendFormat("\\u{0:x4}", int c) |> ignore
            | c -> sb.Append c |> ignore
        sb.Append '"' |> ignore
    | JI i -> sb.Append i |> ignore
    | JB b -> sb.Append(if b then "true" else "false") |> ignore
    | JA xs ->
        sb.Append '[' |> ignore
        xs |> List.iteri (fun i x -> (if i > 0 then sb.Append ',' |> ignore); jwrite sb x)
        sb.Append ']' |> ignore
    | JO kvs ->
        sb.Append '{' |> ignore
        kvs |> List.iteri (fun i (k, v) ->
            (if i > 0 then sb.Append ',' |> ignore)
            jwrite sb (JS k)
            sb.Append ':' |> ignore
            jwrite sb v)
        sb.Append '}' |> ignore

let jsonText (j: J) : string =
    let sb = StringBuilder()
    jwrite sb j
    sb.ToString()

// ---------- запросы ----------

type QueryOpts =
    { Json: bool
      NoBody: bool
      Depth: int }

let defaultOpts = { Json = false; NoBody = false; Depth = 1 }

let kinds = [ "def"; "sig"; "refs"; "callers"; "callees"; "module"; "outline"; "search"; "deps"; "unused" ]

let private firstDoc (d: Def) =
    match d.Doc |> List.tryFind (fun s -> s <> "") with
    | Some s -> if s.Length > 110 then s.Substring(0, 107) + "..." else s
    | None -> ""

let private loc (d: Def) = sprintf "%s:%d" d.File.Rel d.Line
let private modLabel (d: Def) = if d.Module = "" then "global" else d.Module

let private sigLine (d: Def) =
    let parts =
        [ d.Sig
          modLabel d + (if d.Exported then ", exported" else "") + (if d.Kind <> KFn && d.Kind <> KVar then ", " + kindName d.Kind elif d.Kind = KVar then ", var" else "")
          firstDoc d
          loc d ]
    String.Join(" — ", parts |> List.filter (fun s -> s <> ""))

let private defJson (d: Def) =
    JO [ "name", JS d.Name
         "kind", JS (kindName d.Kind)
         "module", JS d.Module
         "exported", JB d.Exported
         "sig", JS d.Sig
         "params", JA (d.Params |> List.map JS)
         "file", JS d.File.Rel
         "line", JI d.Line
         "col", JI d.Col
         "endLine", JI d.EndLine
         "doc", JS (String.Join("\n", d.Doc)) ]

let private bodyText (d: Def) =
    let a = max 1 d.DocStart
    String.Join("\n", d.File.Lines.[a - 1 .. min (d.File.Lines.Length - 1) (d.EndLine - 1)])

let private findDefs (idx: Index) (name: string) : Def list =
    let qual, n =
        match name.IndexOf "::" with
        | k when k > 0 && k + 2 < name.Length -> name.Substring(0, k), name.Substring(k + 2)
        | _ -> null, name
    match idx.ByName.TryGetValue n with
    | true, ds ->
        ds |> Seq.filter (fun d -> isNull qual || d.Module = qual)
        |> Seq.sortBy (fun d -> (if d.File.IsExtra then 1 else 0), d.File.Rel, d.Line)
        |> List.ofSeq
    | _ -> []

let private suggest (idx: Index) (name: string) : string list =
    let q = (match name.IndexOf "::" with k when k > 0 -> name.Substring(k + 2) | _ -> name).ToLowerInvariant()
    let pool =
        seq {
            yield! idx.ByName.Keys
            yield! idx.BuiltinNames ()
            match findRoot () with
            | Some r -> yield! (guideFor r).Keys
            | None -> ()
        } |> Seq.distinct |> Seq.toArray
    let limit = if q.Length <= 4 then 1 else max 2 (q.Length / 4)
    pool
    |> Array.choose (fun c ->
        let cl = c.ToLowerInvariant()
        if abs (c.Length - q.Length) <= limit + 2 && editDistance q cl <= limit then Some (editDistance q cl, c)
        elif q.Length >= 3 && (cl.Contains q || (cl.Length >= 3 && q.Contains cl)) then Some (limit + 1, c)
        else None)
    |> Array.sortBy (fun (d, c) -> d, c.Length, c)
    |> Array.truncate 5 |> Array.map snd |> List.ofArray

let private notFound (idx: Index) (name: string) : string * J =
    let sg = suggest idx name
    let msg =
        if sg.IsEmpty then sprintf "нет такого имени «%s»" name
        else sprintf "нет такого имени «%s»; возможно: %s" name (String.Join(", ", sg))
    msg, JO [ "error", JS msg; "suggestions", JA (sg |> List.map JS) ]

let private builtinInfo (idx: Index) (name: string) : (string * string) option =
    let g = match findRoot () with Some r -> guideFor r | None -> Dictionary()
    match g.TryGetValue name with
    | true, (sg, desc) -> Some (sg, desc)
    | _ -> if idx.IsBuiltin name then Some (name, "") else None

let private builtinLine (name: string) (sg: string, desc: string) =
    let d = if desc.Length > 110 then desc.Substring(0, 107) + "..." else desc
    String.Join(" — ", [ (if sg = name then name else sg); "builtin"; d; "docs/lisp-library-guide.md" ] |> List.filter (fun s -> s <> ""))

let private refKey (r: Ref) = (r.File.Rel, r.Line, r.Col)

// ссылки на заданные определения (имена без определений — по имени)
let private refsTo (idx: Index) (name: string) (defs: Def list) : Ref list =
    let bare = match name.IndexOf "::" with k when k > 0 -> name.Substring(k + 2) | _ -> name
    match idx.RefsByName.TryGetValue bare with
    | true, rs ->
        rs |> Seq.filter (fun r ->
            if defs.IsEmpty then r.Targets.IsEmpty
            else r.Targets |> List.exists (fun t -> defs |> List.exists (fun d -> obj.ReferenceEquals(d, t))))
        |> Seq.filter (fun r -> defs.IsEmpty || isNull r.Owner || not (defs |> List.exists (fun d -> obj.ReferenceEquals(d, r.Owner))))
        |> Seq.sortBy refKey |> List.ofSeq
    | _ -> []

let private loc' (r: Ref) = sprintf "%s:%d" r.File.Rel r.Line
let private ownerLabel (r: Ref) = if isNull r.Owner then r.Label else r.Owner.Name

let private qDef (idx: Index) (name: string) (o: QueryOpts) : string * J =
    match findDefs idx name with
    | [] ->
        match builtinInfo idx name with
        | Some bi ->
            builtinLine name bi, JO [ "name", JS name; "kind", JS "builtin"; "sig", JS (fst bi); "doc", JS (snd bi) ]
        | None ->
            // экспорт без найденного определения
            let exported = idx.Modules |> Seq.tryFind (fun kv -> kv.Value.ExportSet.Contains name)
            match exported with
            | Some kv ->
                let m = sprintf "%s: экспортируется модулем %s, определение не найдено (builtin или порождено макросом)" name kv.Key
                m, JO [ "name", JS name; "module", JS kv.Key; "note", JS m ]
            | None -> notFound idx name
    | ds ->
        let sb = StringBuilder()
        ds |> List.iteri (fun i d ->
            if i > 0 then sb.Append("\n") |> ignore
            sb.AppendFormat("{0}:{1}:{2} {3} ({4}{5})\n", d.File.Rel, d.Line, d.Col, d.Sig, modLabel d + (if d.Exported then ", exported" else ""), ", " + kindName d.Kind) |> ignore
            if not o.NoBody then sb.AppendLine(bodyText d) |> ignore
            elif not d.Doc.IsEmpty then sb.AppendLine(String.Join("\n", d.Doc |> List.map (fun s -> "; " + s))) |> ignore)
        let js = ds |> List.map (fun d ->
                    match defJson d with
                    | JO kv when not o.NoBody -> JO (kv @ [ "body", JS (bodyText d) ])
                    | j -> j)
        sb.ToString().TrimEnd(), JA js

let private qSig (idx: Index) (name: string) : string * J =
    match findDefs idx name with
    | [] ->
        match builtinInfo idx name with
        | Some bi -> builtinLine name bi, JO [ "name", JS name; "kind", JS "builtin"; "sig", JS (fst bi); "doc", JS (snd bi) ]
        | None -> notFound idx name
    | ds -> String.Join("\n", ds |> List.map sigLine), JA (ds |> List.map defJson)

let private qRefs (idx: Index) (name: string) : string * J =
    let ds = findDefs idx name
    if ds.IsEmpty && (builtinInfo idx name).IsNone && not (idx.RefsByName.ContainsKey name) then notFound idx name
    else
        let rs = refsTo idx name ds
        let sb = StringBuilder()
        let owners = rs |> List.map ownerLabel |> List.distinct |> List.length
        sb.AppendFormat("refs {0}: {1} ссылок в {2} определениях/формах\n", name, rs.Length, owners) |> ignore
        for r in rs |> List.truncate 200 do
            sb.AppendFormat("{0}:{1}:{2}  в {3}{4}\n", r.File.Rel, r.Line, r.Col, ownerLabel r, (if r.Quoted then "  ('имя)" else "")) |> ignore
        if rs.Length > 200 then sb.AppendFormat("... ещё {0} (--json — все)\n", rs.Length - 200) |> ignore
        let js =
            JA (rs |> List.map (fun r ->
                    JO [ "file", JS r.File.Rel; "line", JI r.Line; "col", JI r.Col; "in", JS (ownerLabel r); "quoted", JB r.Quoted ]))
        sb.ToString().TrimEnd(), js

// BFS по вызывающим/вызываемым: (глубина, определение или метка, через что)
let private qWalk (idx: Index) (name: string) (depth: int) (callers: bool) : string * J =
    let ds = findDefs idx name
    if ds.IsEmpty then
        match builtinInfo idx name with
        | Some _ when callers ->
            // builtin: вызывающие по имени
            let rs = refsTo idx name []
            let owners = rs |> List.map ownerLabel |> List.distinct
            sprintf "callers %s (builtin): %d\n%s" name owners.Length (String.Join("\n", owners |> List.truncate 100 |> List.map (fun o -> "  " + o))),
            JA (owners |> List.map JS)
        | _ -> notFound idx name
    else
        let seen = HashSet<Def>(HashIdentity.Reference)
        for d in ds do seen.Add d |> ignore
        let result = List<int * string * Def * string>()    // глубина, имя/метка, определение, через
        let builtinsUsed = HashSet<string>()
        let mutable frontier : (Def * string) list = ds |> List.map (fun d -> d, name)
        let mutable level = 1
        while level <= max 1 depth && not frontier.IsEmpty do
            let next = List<Def * string>()
            for (d, via) in frontier do
                if callers then
                    for r in refsTo idx d.Name [ d ] |> List.filter (fun r -> not r.Quoted) do
                        if isNull r.Owner then
                            if level = 1 then result.Add((level, r.Label, null, loc' r))
                        elif seen.Add r.Owner then
                            result.Add((level, r.Owner.Name, r.Owner, via))
                            next.Add((r.Owner, r.Owner.Name))
                else
                    match idx.RefsByOwner.TryGetValue d with
                    | true, rs ->
                        for r in rs |> Seq.filter (fun r -> not r.Quoted) do
                            if r.Targets.IsEmpty then
                                if idx.IsBuiltin r.Name && not r.Quoted then builtinsUsed.Add r.Name |> ignore
                            else
                                for t in r.Targets do
                                    if seen.Add t then
                                        result.Add((level, t.Name, t, via))
                                        next.Add((t, t.Name))
                    | _ -> ()
            frontier <- List.ofSeq next
            level <- level + 1
        let sb = StringBuilder()
        let dir = if callers then "callers" else "callees"
        sb.AppendFormat("{0} {1} (глубина {2}): {3}\n", dir, name, max 1 depth, result.Count) |> ignore
        let rows = result |> Seq.sortBy (fun (l, n, d, _) -> l, (if isNull d then "" else d.File.Rel), (if isNull d then 0 else d.Line)) |> List.ofSeq
        for (l, n, d, via) in rows do
            let where = if isNull d then via else loc d
            let sgn = if isNull d then n else d.Sig
            sb.AppendFormat("{0}{1}  {2}{3}\n", (if depth > 1 then sprintf "%d " l else ""), sgn, where,
                            (if depth > 1 && l > 1 && not (isNull d) then "  <- " + via else "")) |> ignore
        if not callers && builtinsUsed.Count > 0 then
            sb.AppendFormat("builtin: {0}\n", String.Join(" ", builtinsUsed |> Seq.sort)) |> ignore
        let js =
            JO [ "name", JS name
                 "depth", JI (max 1 depth)
                 "items", JA (rows |> List.map (fun (l, n, d, via) ->
                                JO ([ "depth", JI l; "name", JS n; "via", JS via ]
                                    @ (if isNull d then [] else [ "file", JS d.File.Rel; "line", JI d.Line; "module", JS d.Module ]))))
                 "builtins", JA (builtinsUsed |> Seq.sort |> Seq.map JS |> List.ofSeq) ]
        sb.ToString().TrimEnd(), js

// внешние зависимости набора файлов: модуль -> имена (только определения других модулей)
let private depsOf (idx: Index) (files: HashSet<FileInfo>) (self: string) : (string * string list) list * string list =
    let byMod = Dictionary<string, SortedSet<string>>()
    let builtins = SortedSet<string>()
    for r in idx.Refs do
        if files.Contains r.File && not r.Quoted then
            match r.Targets with
            | [] -> if idx.IsBuiltin r.Name then builtins.Add r.Name |> ignore
            | t :: _ ->
                if not (files.Contains t.File) && t.Module <> self then
                    let m = if t.Module = "" then "global" else t.Module
                    if not (byMod.ContainsKey m) then byMod.[m] <- SortedSet<string>()
                    byMod.[m].Add t.Name |> ignore
    (byMod |> Seq.sortBy (fun kv -> kv.Key) |> Seq.map (fun kv -> kv.Key, List.ofSeq kv.Value) |> List.ofSeq), List.ofSeq builtins

let private depsText (deps: (string * string list) list, builtins: string list) =
    let lines = deps |> List.map (fun (m, ns) -> sprintf "  %s: %s" m (String.Join(" ", ns)))
    let b = if builtins.IsEmpty then [] else [ sprintf "  builtin: %s" (String.Join(" ", builtins)) ]
    String.Join("\n", lines @ b)

let private depsJson (deps: (string * string list) list, builtins: string list) =
    JA ((deps |> List.map (fun (m, ns) -> JO [ "module", JS m; "names", JA (ns |> List.map JS) ]))
        @ (if builtins.IsEmpty then [] else [ JO [ "module", JS "builtin"; "names", JA (builtins |> List.map JS) ] ]))

let private qModule (idx: Index) (name: string) : string * J =
    match idx.Modules.TryGetValue name with
    | true, mi ->
        let exps =
            mi.Exports |> Seq.map (fun e ->
                let d =
                    match idx.ByName.TryGetValue e with
                    | true, ds -> ds |> Seq.tryFind (fun d -> d.Module = name)
                    | _ -> None
                e, d) |> List.ofSeq
        let files = HashSet<FileInfo>(mi.Files, HashIdentity.Reference)
        let deps = depsOf idx files name
        let sb = StringBuilder()
        sb.AppendFormat("module {0}: файлы {1}; экспортов {2}\n", name, String.Join(", ", mi.Files |> Seq.map (fun f -> f.Rel)), mi.Exports.Count) |> ignore
        for (e, d) in exps do
            match d with
            | Some d ->
                sb.AppendLine(String.Join(" — ", [ d.Sig; firstDoc d; loc d ] |> List.filter (fun s -> s <> ""))) |> ignore
            | None -> sb.AppendLine(e + " — (определение не найдено: builtin или порождено макросом)") |> ignore
        sb.AppendLine("зависит от:") |> ignore
        sb.Append(depsText deps) |> ignore
        sb.ToString().TrimEnd(),
        JO [ "name", JS name
             "files", JA (mi.Files |> Seq.map (fun f -> JS f.Rel) |> List.ofSeq)
             "exports", JA (exps |> List.map (fun (e, d) ->
                              match d with
                              | Some d -> defJson d
                              | None -> JO [ "name", JS e; "found", JB false ]))
             "deps", depsJson deps ]
    | _ ->
        let names = idx.Modules.Keys |> Seq.toArray
        let sg = names |> Array.filter (fun m -> editDistance (name.ToLowerInvariant()) (m.ToLowerInvariant()) <= 2 || m.Contains name) |> Array.sortBy (fun m -> editDistance (name.ToLowerInvariant()) (m.ToLowerInvariant()), m) |> Array.truncate 5
        let msg = sprintf "нет такого модуля «%s»%s. Модули: %s" name (if sg.Length > 0 then "; возможно: " + String.Join(", ", sg) else "") (String.Join(" ", names |> Array.sort))
        msg, JO [ "error", JS msg ]

let private findFile (idx: Index) (arg: string) : FileInfo option =
    let a = cleanPath arg
    let a = if a.StartsWith "./" then a.Substring 2 else a
    let full = (try cleanPath (IO.Path.GetFullPath arg) with _ -> a)
    let rootN = cleanPath idx.Root
    let cands = idx.Files |> Seq.toList
    match cands |> List.tryFind (fun f -> String.Equals(f.Rel, a, StringComparison.OrdinalIgnoreCase)) with
    | Some f -> Some f
    | None ->
        match cands |> List.tryFind (fun f -> String.Equals(cleanPath (IO.Path.Combine(rootN, f.Rel)), full, StringComparison.OrdinalIgnoreCase)) with
        | Some f -> Some f
        | None ->
            let hits = cands |> List.filter (fun f -> f.Rel.EndsWith("/" + a, StringComparison.OrdinalIgnoreCase) || f.Rel.EndsWith(a, StringComparison.OrdinalIgnoreCase))
            match hits |> List.sortBy (fun f -> f.IsExtra, f.Rel.Length) with
            | f :: _ -> Some f
            | [] -> None

let private fileNotFoundMsg (idx: Index) (arg: string) =
    let part = IO.Path.GetFileNameWithoutExtension arg
    let sg = idx.Files |> Seq.filter (fun f -> not f.IsExtra && f.Rel.Contains part) |> Seq.truncate 5 |> Seq.map (fun f -> f.Rel) |> List.ofSeq
    sprintf "нет такого файла «%s»%s" arg (if sg.IsEmpty then "" else "; возможно: " + String.Join(", ", sg))

let private qOutline (idx: Index) (arg: string) : string * J =
    match findFile idx arg with
    | None ->
        let m = fileNotFoundMsg idx arg
        m, JO [ "error", JS m ]
    | Some fi ->
        let ds = idx.Defs |> Seq.filter (fun d -> obj.ReferenceEquals(d.File, fi)) |> Seq.sortBy (fun d -> d.Line) |> List.ofSeq
        let sb = StringBuilder()
        sb.AppendFormat("{0} (модуль {1}, {2} строк, {3} определений; * — экспорт)\n", fi.Rel, (if fi.Module = "" then "—" else fi.Module), fi.Lines.Length, ds.Length) |> ignore
        for d in ds do
            let doc = (let s = firstDoc d in if s.Length > 80 then s.Substring(0, 77) + "..." else s)
            sb.AppendFormat("{0,5} {1,-6} {2}{3}{4}\n", d.Line, kindName d.Kind, (if d.Exported then "*" else ""), d.Sig, (if doc = "" then "" else " — " + doc)) |> ignore
        sb.ToString().TrimEnd(), JO [ "file", JS fi.Rel; "module", JS fi.Module; "lines", JI fi.Lines.Length; "defs", JA (ds |> List.map defJson) ]

// Корпус поиска: определения lib (имя, комментарий, строка справочника, модуль) + builtin только из справочника
type private SearchData =
    { Corpus: SearchText.Corpus
      Items: (string * J)[]
      Exported: bool[]
      Names: string[]
      Glossary: SearchText.Glossary }

let private searchData (idx: Index) : SearchData =
    lock idx (fun () ->
        match idx.SearchCache with
        | :? SearchData as sd -> sd
        | _ ->
            let guide = guideFor idx.Root
            let defs = idx.Defs |> Seq.filter (fun d -> not d.File.IsExtra) |> Array.ofSeq
            let gdesc (d: Def) =
                if d.Exported || d.Module = "" then (match guide.TryGetValue d.Name with | true, (_, desc) -> desc | _ -> "") else ""
            let defDocs =
                defs |> Array.map (fun d ->
                    [ 4.0, SearchText.tokenizeName d.Name
                      2.0, SearchText.tokenize (String.Join(" ", d.Doc))
                      1.5, SearchText.tokenize (gdesc d)
                      1.0, SearchText.tokenize d.Module ])
            let only = guide |> Seq.filter (fun kv -> not (idx.ByName.ContainsKey kv.Key)) |> Seq.sortBy (fun kv -> kv.Key) |> Array.ofSeq
            let onlyDocs =
                only |> Array.map (fun kv ->
                    [ 4.0, SearchText.tokenizeName kv.Key
                      1.5, SearchText.tokenize (snd kv.Value)
                      1.0, [ "builtin" ] ])
            let items =
                Array.append
                    (defs |> Array.map (fun d -> sigLine d, defJson d))
                    (only |> Array.map (fun kv ->
                        builtinLine kv.Key kv.Value, JO [ "name", JS kv.Key; "kind", JS "builtin"; "sig", JS (fst kv.Value); "doc", JS (snd kv.Value) ]))
            let glossary =
                let p = IO.Path.Combine(idx.Root, "docs", "search-glossary.txt")
                if IO.File.Exists p then SearchText.parseGlossary (IO.File.ReadAllLines p) else []
            let sd =
                { Corpus = SearchText.Corpus(List.ofArray (Array.append defDocs onlyDocs))
                  Items = items
                  Exported = Array.append (defs |> Array.map (fun d -> d.Exported)) (Array.create only.Length false)
                  Names = Array.append (defs |> Array.map (fun d -> d.Name.ToLowerInvariant())) (only |> Array.map (fun kv -> kv.Key.ToLowerInvariant()))
                  Glossary = glossary }
            idx.SearchCache <- box sd
            sd)

// search: BM25 по стемам (поля: имя > комментарий > строка справочника > модуль), глоссарий, триграммы; альтернативы через «|»
let private qSearch (idx: Index) (text: string) : string * J =
    let alts = text.Split('|') |> Array.map (fun s -> s.Trim()) |> Array.filter (fun s -> s <> "")
    if alts.Length = 0 || (SearchText.tokenize text).IsEmpty && not (text.Contains "-") then
        "search: пустой запрос", JO [ "error", JS "пустой запрос" ]
    else
        let sd = searchData idx
        let best = Array.zeroCreate<float> sd.Items.Length
        for a in alts do
            let sc = SearchText.scoreAlternative sd.Corpus sd.Glossary a
            let al = a.ToLowerInvariant()
            for i in 0 .. best.Length - 1 do
                // точное имя — всегда выше любых текстовых совпадений
                let s = if sd.Names.[i] = al then sc.[i] + 1000.0 else sc.[i]
                if s > best.[i] then best.[i] <- s
        let scored =
            [ for i in 0 .. best.Length - 1 do
                if best.[i] > 0.0 then yield (best.[i] * (if sd.Exported.[i] then 1.1 else 1.0), i) ]
            |> List.sortBy (fun (s, i) -> -s, i) |> List.truncate 10
        if scored.IsEmpty then sprintf "search %s: ничего не найдено" text, JA []
        else String.Join("\n", scored |> List.map (fun (_, i) -> fst sd.Items.[i])), JA (scored |> List.map (fun (_, i) -> snd sd.Items.[i]))

let private qDeps (idx: Index) (arg: string) : string * J =
    match findFile idx arg with
    | None ->
        let m = fileNotFoundMsg idx arg
        m, JO [ "error", JS m ]
    | Some fi ->
        let deps = depsOf idx (HashSet<FileInfo>([ fi ], HashIdentity.Reference)) fi.Module
        sprintf "deps %s:\n%s" fi.Rel (depsText deps), JO [ "file", JS fi.Rel; "deps", depsJson deps ]

let private qUnused (idx: Index) : string * J =
    let used (d: Def) = not (refsTo idx d.Name [ d ]).IsEmpty
    let cand =
        idx.Defs |> Seq.filter (fun d -> not d.File.IsExtra && (d.Kind = KFn || d.Kind = KVar || d.Kind = KMacro))
        |> Seq.filter (fun d -> not (used d)) |> List.ofSeq
    let priv = cand |> List.filter (fun d -> not d.Exported) |> List.sortBy (fun d -> d.File.Rel, d.Line)
    let exp = cand |> List.filter (fun d -> d.Exported) |> List.sortBy (fun d -> d.File.Rel, d.Line)
    let lines (ds: Def list) = ds |> List.map (fun d -> sprintf "  %s:%d %s (%s)" d.File.Rel d.Line d.Sig (kindName d.Kind))
    let text =
        String.Join("\n",
            [ sprintf "приватные без ссылок: %d" priv.Length ] @ lines priv
            @ [ sprintf "экспорт без ссылок в lib/tests/examples/bench: %d" exp.Length ] @ lines exp)
    text, JO [ "private", JA (priv |> List.map defJson); "exportedUnreferenced", JA (exp |> List.map defJson) ]

// Выполнить запрос: (вывод, успех). Для json вывод — JSON-текст.
let run (idx: Index) (kind: string) (arg: string) (o: QueryOpts) : string * bool =
    let res =
        match kind.ToLowerInvariant() with
        | "unused" -> Some (qUnused idx)
        | k when String.IsNullOrWhiteSpace arg && List.contains k kinds ->
            Some (sprintf "%s: нужен аргумент" k, JO [ "error", JS (k + ": нужен аргумент") ])
        | "def" -> Some (qDef idx arg o)
        | "sig" -> Some (qSig idx arg)
        | "refs" -> Some (qRefs idx arg)
        | "callers" -> Some (qWalk idx arg o.Depth true)
        | "callees" -> Some (qWalk idx arg o.Depth false)
        | "module" -> Some (qModule idx arg)
        | "outline" -> Some (qOutline idx arg)
        | "search" -> Some (qSearch idx arg)
        | "deps" -> Some (qDeps idx arg)
        | _ -> None
    match res with
    | None ->
        let m = sprintf "неизвестный вид запроса «%s»; есть: %s" kind (String.Join(" ", kinds))
        (if o.Json then jsonText (JO [ "error", JS m ]) else m), false
    | Some (text, j) ->
        let ok = (match j with JO (("error", _) :: _) -> false | _ -> not (text.StartsWith "нет такого"))
        (if o.Json then jsonText j else text), ok
