// Текстовый поиск по коду (Lisp.exe --query search): токенизация, стемминг (рус./англ.), глоссарий, BM25 по полям, триграммы.
// Без внешних зависимостей; используется CodeIndex.qSearch.
module SearchText

open System
open System.Collections.Generic
open System.Text.RegularExpressions

// ---------- стемминг ----------

let private isCyr (s: string) = s |> Seq.exists (fun c -> c >= 'Ѐ' && c <= 'ӿ')
let private ruVowels = "аеиоуыэюя".ToCharArray()

let private endsAt (w: string) (e: string) = w.EndsWith(e, StringComparison.Ordinal)

// самое длинное окончание из plain, либо из aya (перед ним «а»/«я»), целиком не левее lo
let private findEnd (w: string) (lo: int) (plain: string list) (aya: string list) : string option =
    let c1 = plain |> List.filter (fun e -> endsAt w e && w.Length - e.Length >= lo)
    let c2 =
        aya |> List.filter (fun e ->
            endsAt w e && w.Length - e.Length >= max lo 1
            && (let c = w.[w.Length - e.Length - 1] in c = 'а' || c = 'я'))
    match c1 @ c2 with
    | [] -> None
    | l -> Some (List.maxBy String.length l)

let private cut (w: string) (e: string) = w.Substring(0, w.Length - e.Length)

let private gerund2 = [ "ив"; "ивши"; "ившись"; "ыв"; "ывши"; "ывшись" ]
let private gerund1 = [ "в"; "вши"; "вшись" ]
let private adjective = [ "ее"; "ие"; "ые"; "ое"; "ими"; "ыми"; "ей"; "ий"; "ый"; "ой"; "ем"; "им"; "ым"; "ом"; "его"; "ого"; "ему"; "ому"; "их"; "ых"; "ую"; "юю"; "ая"; "яя"; "ою"; "ею" ]
let private participle2 = [ "ивш"; "ывш"; "ующ" ]
let private participle1 = [ "ем"; "нн"; "вш"; "ющ"; "щ" ]
let private verb2 = [ "ила"; "ыла"; "ена"; "ейте"; "уйте"; "ите"; "или"; "ыли"; "ей"; "уй"; "ил"; "ыл"; "им"; "ым"; "ен"; "ило"; "ыло"; "ено"; "ят"; "ует"; "уют"; "ит"; "ыт"; "ены"; "ить"; "ыть"; "ишь"; "ую"; "ю" ]
let private verb1 = [ "ла"; "на"; "ете"; "йте"; "ли"; "й"; "л"; "ем"; "н"; "ло"; "но"; "ет"; "ют"; "ны"; "ть"; "ешь"; "нно" ]
let private noun = [ "а"; "ев"; "ов"; "ие"; "ье"; "е"; "иями"; "ями"; "ами"; "еи"; "ии"; "и"; "ией"; "ей"; "ой"; "ий"; "й"; "иям"; "ям"; "ием"; "ем"; "ам"; "ом"; "о"; "у"; "ах"; "иях"; "ях"; "ы"; "ь"; "ю"; "ию"; "ью"; "я" ]

// упрощённый Snowball Russian (ё -> е)
let ruStem (word: string) : string =
    let w = word.Replace('ё', 'е')
    let rv = match w.IndexOfAny ruVowels with -1 -> w.Length | i -> i + 1
    let regionAfter (start: int) =
        // позиция после первой «согласной после гласной», начиная с start
        let mutable i = start
        let n = w.Length
        let isV k = Array.contains w.[k] ruVowels
        while i < n && not (isV i) do i <- i + 1
        while i < n && isV i do i <- i + 1
        if i < n then i + 1 else n
    let r1 = regionAfter 0
    let r2 = regionAfter r1
    let step1 =
        match findEnd w rv gerund2 gerund1 with
        | Some e -> cut w e
        | None ->
            let w1 = (match findEnd w rv [ "ся"; "сь" ] [] with Some e -> cut w e | None -> w)
            match findEnd w1 rv adjective [] with
            | Some e ->
                let a = cut w1 e
                match findEnd a rv participle2 participle1 with
                | Some p -> cut a p
                | None -> a
            | None ->
                match findEnd w1 rv verb2 verb1 with
                | Some e -> cut w1 e
                | None ->
                    match findEnd w1 rv noun [] with
                    | Some e -> cut w1 e
                    | None -> w1
    let step2 = if endsAt step1 "и" && step1.Length - 1 >= rv then cut step1 "и" else step1
    let step3 =
        if endsAt step2 "ость" && step2.Length - 4 >= r2 then cut step2 "ость"
        elif endsAt step2 "ост" && step2.Length - 3 >= r2 then cut step2 "ост"
        else step2
    let step4 =
        if endsAt step3 "нн" then step3.Substring(0, step3.Length - 1)
        elif endsAt step3 "ейше" && step3.Length - 4 >= rv then (let s = cut step3 "ейше" in if endsAt s "нн" then s.Substring(0, s.Length - 1) else s)
        elif endsAt step3 "ейш" && step3.Length - 3 >= rv then (let s = cut step3 "ейш" in if endsAt s "нн" then s.Substring(0, s.Length - 1) else s)
        elif endsAt step3 "ь" then cut step3 "ь"
        else step3
    if step4.Length >= 2 then step4 else w

// простое отсечение английских суффиксов (две стадии: словоизменение, затем словообразование)
let enStem (w: string) : string =
    let tryCut (s: string) (rules: (string * string) list) =
        match rules |> List.tryFind (fun (suf, _) -> endsAt s suf && s.Length - suf.Length >= 3) with
        | Some (suf, rep) -> cut s suf + rep
        | None -> s
    if w.Length <= 3 || w |> Seq.exists Char.IsDigit then w
    else
        let s1 =
            if endsAt w "ies" && w.Length > 4 then cut w "ies" + "y"
            elif endsAt w "ing" && w.Length > 5 then cut w "ing"
            elif endsAt w "ed" && w.Length > 4 then cut w "ed"
            elif (endsAt w "sses" || endsAt w "xes" || endsAt w "zes" || endsAt w "ches" || endsAt w "shes") && w.Length > 4 then cut w "es"
            elif endsAt w "s" && not (endsAt w "ss" || endsAt w "us" || endsAt w "is") then cut w "s"
            else w
        let s2 =
            tryCut s1 [ "izations", ""; "ization", ""; "isation", ""; "ations", ""; "ation", ""; "ities", ""; "ity", ""; "ments", ""; "ment", ""; "ive", ""; "ous", ""; "ate", ""; "al", "" ]
        let s3 = if endsAt s2 "e" && s2.Length > 4 then cut s2 "e" else s2
        if s3.Length >= 3 then s3 else w

let private stopwords =
    HashSet<string>([ "и"; "в"; "во"; "на"; "по"; "с"; "со"; "к"; "ко"; "из"; "от"; "до"; "за"; "о"; "об"; "у"; "а"; "но"; "или"; "для"; "над"; "под"; "при"; "как"; "что"; "это"; "не"; "ли"
                      "the"; "of"; "a"; "an"; "and"; "or"; "in"; "on"; "to"; "for"; "with"; "by"; "is"; "are"; "be"; "at"; "as"; "from"; "it"; "its"; "that"; "this" ])

let stem (w: string) : string = if isCyr w then ruStem w else enStem w

let private splitRe = Regex(@"[^\p{L}\p{N}]+", RegexOptions.Compiled)

// слова текста -> стемы (без стоп-слов; одиночные буквы отбрасываются, цифры нет)
let tokenize (text: string) : string list =
    splitRe.Split(text.ToLowerInvariant().Replace('ё', 'е'))
    |> Array.filter (fun t -> t <> "" && (t.Length >= 2 || Char.IsDigit t.[0]) && not (stopwords.Contains t))
    |> Array.map stem
    |> List.ofArray

// идентификатор: части по разделителям + целое имя (если составное)
let tokenizeName (name: string) : string list =
    let n = name.ToLowerInvariant().Replace('ё', 'е')
    let parts = tokenize n
    let whole = Regex.Replace(n, @"[^\p{L}\p{N}]+", "-").Trim('-')
    if whole.Contains "-" then whole :: parts else parts

// ---------- глоссарий ----------

// группа эквивалентных терминов; термин — список стемов (фраза)
type Glossary = (string list) list list

let parseGlossary (lines: string seq) : Glossary =
    [ for l in lines do
        let t = l.Trim()
        if t <> "" && not (t.StartsWith "#") then
            let entries = t.Split('|') |> Array.map tokenize |> Array.filter (fun e -> not e.IsEmpty) |> List.ofArray
            if entries.Length >= 2 then yield entries ]

// термины запроса -> дополнительные термины (по глоссарию), каждый один раз
// Результат: (дополнительные термы с весами, слова, поглощённые сработавшей фразой — их прямой вес снижается).
// Фраза из нескольких слов (square free, дифференциальное уравнение) — точный термин: её слова теряют вес, замены весят больше.
let expand (g: Glossary) (q: HashSet<string>) : (string * float) list * HashSet<string> =
    let demoted = HashSet<string>()
    let acc = Dictionary<string, float>()
    // слово запроса совпадает с термином глоссария, если основы равны или одна — начало другой (разница ≤ 2 букв, длина ≥ 5):
    // стеммер даёт разные основы у «бесквадратное» и «бесквадратое» (опечатка)
    let hit (e: string) =
        q.Contains e
        || (e.Length >= 5 && q |> Seq.exists (fun t -> t.Length >= 5 && abs (t.Length - e.Length) <= 2 && (t.StartsWith(e, StringComparison.Ordinal) || e.StartsWith(t, StringComparison.Ordinal))))
    for grp in g do
        for e in grp do
            if e |> List.forall hit then
                let phrase = e.Length >= 2
                if phrase then for t in e do demoted.Add t |> ignore
                for other in grp do
                    if not (obj.ReferenceEquals(other, e)) then
                        for t in other do
                            let w = if phrase then 0.9 else 0.6
                            if not (q.Contains t) || demoted.Contains t then
                                acc.[t] <- (match acc.TryGetValue t with | true, v -> max v w | _ -> w)
    [ for kv in acc -> kv.Key, kv.Value ], demoted

// ---------- BM25 по полям ----------

let private trigrams (s: string) =
    let p = "^" + s + "$"
    HashSet<string>([ for i in 0 .. p.Length - 3 -> p.Substring(i, 3) ])

let private dice (a: HashSet<string>) (b: HashSet<string>) =
    if a.Count = 0 || b.Count = 0 then 0.0
    else
        let mutable c = 0
        for x in a do if b.Contains x then c <- c + 1
        2.0 * float c / float (a.Count + b.Count)

type Corpus(docs: (float * string list) list list) =
    let n = docs.Length
    let postings = Dictionary<string, List<struct (int * float)>>()
    let lens = Array.zeroCreate<float> n
    do
        docs |> List.iteri (fun i fields ->
            let tf = Dictionary<string, float>()
            for (w, toks) in fields do
                for t in toks do
                    lens.[i] <- lens.[i] + w
                    tf.[t] <- (match tf.TryGetValue t with | true, v -> v + w | _ -> w)
            for kv in tf do
                if not (postings.ContainsKey kv.Key) then postings.[kv.Key] <- List()
                postings.[kv.Key].Add(struct (i, kv.Value)))
    let avg = if n = 0 then 1.0 else max 1.0 (Array.sum lens / float n)
    member _.Size = n
    member _.Has(t: string) = postings.ContainsKey t
    member _.Vocabulary = postings.Keys
    // запрос: (терм, вес) -> оценки документов
    member _.Score(q: (string * float) list) : float[] =
        let sc = Array.zeroCreate<float> n
        let k1, b = 1.2, 0.75
        for (t, qw) in q do
            match postings.TryGetValue t with
            | true, ps ->
                let df = float ps.Count
                let idf = (log (1.0 + (float n - df + 0.5) / (df + 0.5))) ** 1.5
                for struct (d, tf) in ps do
                    sc.[d] <- sc.[d] + qw * idf * tf * (k1 + 1.0) / (tf + k1 * (1.0 - b + b * lens.[d] / avg))
            | _ -> ()
        sc
    // близкие по триграммам термы словаря (для терма без попаданий)
    member this.Similar(t: string) : (string * float) list =
        let tg = trigrams t
        [ for v in postings.Keys do
            if abs (v.Length - t.Length) <= 3 then
                let s = dice tg (trigrams v)
                if s >= 0.5 then yield v, s ]
        |> List.sortBy (fun (_, s) -> -s) |> List.truncate 4

// Запрос (одна альтернатива) -> оценки документов
let scoreAlternative (c: Corpus) (g: Glossary) (alt: string) : float[] =
    let rawWords = Regex.Split(alt.ToLowerInvariant(), @"\s+") |> Array.filter (fun s -> s <> "")
    let direct = List<string * float>()
    let seen = HashSet<string>()
    let add (t: string) (w: float) = if seen.Add t then direct.Add((t, w))
    for w in rawWords do
        // составное имя с дефисом — целиком
        if w.Contains "-" && w.Length > 2 then add (Regex.Replace(w, @"[^\p{L}\p{N}]+", "-").Trim('-')) 1.0
        for t in tokenize w do add t 1.0
    // термы без попаданий: близкие по триграммам (опечатки, незнакомые формы); лучший из них участвует и в расширении глоссарием
    let fuzzy =
        [ for (t, _) in direct do
            if not (c.Has t) && t.Length >= 4 then
                for (i, (v, s)) in List.indexed (c.Similar t) -> v, (if i = 0 then 0.8 else 0.3) * s ]
    let qset = HashSet<string>(seen)
    for (v, _) in fuzzy |> List.truncate 1 do qset.Add v |> ignore
    let extra, demoted = expand g qset
    let directW = [ for (t, w) in direct -> t, (if demoted.Contains t then 0.3 else w) ]
    let terms = directW @ extra @ fuzzy
    // повторы терма — максимум веса
    let merged = terms |> List.groupBy fst |> List.map (fun (t, l) -> t, l |> List.map snd |> List.max)
    c.Score merged
