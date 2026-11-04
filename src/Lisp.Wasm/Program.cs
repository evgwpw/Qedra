// WASM.1: C#-хост (JSExport работает в C#; ядро — F# Lisp.Core).
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Reflection;
using System.Runtime.InteropServices.JavaScript;
using System.Runtime.Versioning;
using System.Text;
using Microsoft.FSharp.Collections;

namespace Lisp.Wasm
{
    [SupportedOSPlatform("browser")]
    public static partial class Exports
    {
        public static void Main() { }

        private static Types.Env? env;
        private static bool filesReady;
        // WASM.1 / М4: тесты идут по одному файлу за вызов; два вызова одновременно не нужны
        private static readonly object testGate = new();

        // WASM.1: lib/** и tests/** встроены в сборку — пишем их в виртуальную ФС
        private static int WriteResources(string subdir)
        {
            var asm = Assembly.GetExecutingAssembly();
            var baseDir = AppContext.BaseDirectory;
            var marker = subdir + "/";
            var written = 0;
            foreach (var res in asm.GetManifestResourceNames())
            {
                var norm = res.Replace('\\', '/');
                if (!norm.StartsWith(marker, StringComparison.OrdinalIgnoreCase)) continue;
                if (!norm.EndsWith(".lisp", StringComparison.OrdinalIgnoreCase)) continue;
                var rel = norm.Substring(marker.Length);
                var path = Path.Combine(baseDir, subdir, rel.Replace('/', Path.DirectorySeparatorChar));
                var dir = Path.GetDirectoryName(path);
                if (!string.IsNullOrEmpty(dir)) Directory.CreateDirectory(dir);
                using var s = asm.GetManifestResourceStream(res)!;
                using var f = File.Create(path);
                s.CopyTo(f);
                written++;
            }
            return written;
        }

        private static void EnsureFiles()
        {
            if (filesReady) return;
            // М3: в браузере стек интерпретатора — это стек JS (около 1 МБ, не настраивается), и RangeError
            // «Maximum call stack size exceeded» приходит раньше, чем RuntimeHelpers.TryEnsureSufficientExecutionStack
            // успевает отказать (в WASM он всегда «достаточно»). Нативная граница измерена: нехвостовая рекурсия
            // держит 1100 кадров, на 1150 страница падает. Логический предел ниже границы даёт обычную ошибку Lisp
            // «Превышена глубина рекурсии» вместо аварийного переполнения (замечание 2в карточки). Ставится здесь,
            // а не в Main: браузерный шаблон не вызывает управляемую точку входа.
            global::Debug.maxDepth = 1000;
            var written = WriteResources("lib");
            WriteResources("tests");
            filesReady = true;
            if (!File.Exists(Path.Combine(AppContext.BaseDirectory, "lib", "prelude.lisp")))
                throw new InvalidOperationException(
                    "lib/prelude.lisp не записан (записано " + written + "); base=" + AppContext.BaseDirectory);
        }

        private static Types.Env GetEnv()
        {
            if (env != null) return env;
            EnsureFiles();
            env = Evaluator.newEnv();
            return env;
        }

        private static string Esc(string s)
        {
            var sb = new StringBuilder();
            foreach (var c in s)
            {
                switch (c)
                {
                    case '"': sb.Append("\\\""); break;
                    case '\\': sb.Append("\\\\"); break;
                    case '\n': sb.Append("\\n"); break;
                    case '\r': sb.Append("\\r"); break;
                    case '\t': sb.Append("\\t"); break;
                    default: sb.Append(c); break;
                }
            }
            return sb.ToString();
        }

        private static string Opt(string s) => s.Length == 0 ? "null" : "\"" + Esc(s) + "\"";

        private static string Answer(string status, string result, string pretty, string latex, string err) =>
            "{\"status\":\"" + status + "\",\"result\":" + Opt(result) + ",\"pretty\":" + Opt(pretty) +
            ",\"latex\":" + Opt(latex) + ",\"note\":null,\"ok\":" + (status == "error" ? "false" : "true") +
            ",\"error\":" + Opt(err) + ",\"stack\":null}";

        private static Types.LispValue Sym(string name) => Types.LispValue.NewLispSym(name);

        private static Types.LispValue List(params Types.LispValue[] items) =>
            Types.LispValue.NewLispList(ListModule.OfSeq(items));

        [JSExport]
        public static string Eval(string code, string mode)
        {
            try
            {
                var e = GetEnv();
                if (mode == "math")
                {
                    // Шаг WASM.JSON: тот же ответ, что у `Lisp.exe --json` с op "math" (status, note, conditions, output, …) —
                    // общий код AgentApi.handleJsonRequest из Lisp.Core
                    var req = "{\"op\":\"math\",\"code\":" + System.Text.Json.JsonSerializer.Serialize(code) + "}";
                    return AgentApi.handleJsonRequest(e, req);
                }
                else
                {
                    // Вычисляем ВСЕ формы текста (как при загрузке файла), возвращаем последнюю:
                    // иначе файл вида web/app/steps.lisp с несколькими define определял бы только последний.
                    var vs = Reader.readAllFrom("<wasm>", code);
                    Types.LispValue res = null!;
                    var count = 0;
                    foreach (var v in vs) { res = Evaluator.eval(v, e); count++; }
                    if (count == 0) return Answer("answer", "nil", "nil", "nil", "");
                    return Answer("answer", Printer.prettyPrint(res), MathPrinter.mathPrint(res), LatexPrinter.latexPrint(res), "");
                }
            }
            catch (Exception ex)
            {
                var sb = new StringBuilder();
                var e = ex;
                var depth = 0;
                while (e != null && depth < 5)
                {
                    if (depth > 0) sb.Append(" <- ");
                    sb.Append(e.GetType().Name).Append(": ").Append(e.Message);
                    e = e.InnerException;
                    depth++;
                }
                var full = ex.ToString();
                if (full.Length > 3000) full = full.Substring(0, 3000);
                sb.Append(" || ").Append(full);
                return Answer("error", "", "", "", sb.ToString());
            }
        }

        // WASM.1 / М4: список файлов tests/lisp/*.lisp (они встроены в сборку как ресурсы tests/…)
        [JSExport]
        public static string TestFiles()
        {
            try
            {
                EnsureFiles();
                var dir = Path.Combine(AppContext.BaseDirectory, "tests");
                var files = Directory.Exists(dir) ? Directory.GetFiles(dir, "*.lisp") : Array.Empty<string>();
                Array.Sort(files, StringComparer.Ordinal);
                var sb = new StringBuilder("[");
                for (var i = 0; i < files.Length; i++)
                {
                    if (i > 0) sb.Append(',');
                    sb.Append('"').Append(Esc(Path.GetFileName(files[i]))).Append('"');
                }
                return sb.Append(']').ToString();
            }
            catch (Exception ex)
            {
                return "{\"error\":\"" + Esc(ex.Message) + "\"}";
            }
        }

        // WASM.1 / М4: один файл Lisp-тестов — свежее окружение (как в настольном LispFileTests.fs),
        // загрузка файла, затем (run-tests). Провалы ловит try внутри run-tests, поэтому считаем
        // напечатанные строки «ok   имя» / «FAIL имя: сообщение».
        [JSExport]
        public static string RunTestFile(string name)
        {
            lock (testGate)
            {
                var sw = Stopwatch.StartNew();
                var file = Path.GetFileName(name ?? "");
                var loadError = "";
                var runError = "";
                var passed = 0;
                var failed = 0;
                var total = 0;
                var failures = new List<string>();
                try
                {
                    EnsureFiles();
                    var path = Path.Combine(AppContext.BaseDirectory, "tests", file);
                    if (!File.Exists(path))
                        return "{\"file\":\"" + Esc(file) + "\",\"error\":\"нет файла tests/" + Esc(file) + "\"}";
                    var e = Evaluator.newEnv();
                    try
                    {
                        Evaluator.loadIntoEnv(path, e);
                    }
                    catch (Exception ex)
                    {
                        loadError = global::Debug.formatError(ex);
                    }
                    if (loadError.Length == 0)
                    {
                        var buf = new StringWriter();
                        var oldOut = Console.Out;
                        try
                        {
                            Console.SetOut(buf);
                            Evaluator.eval(List(Sym("run-tests")), e);
                        }
                        catch (Exception ex)
                        {
                            runError = global::Debug.formatError(ex);
                        }
                        finally
                        {
                            Console.SetOut(oldOut);
                        }
                        foreach (var raw in buf.ToString().Split('\n'))
                        {
                            var line = raw.TrimEnd('\r');
                            if (line.StartsWith("ok", StringComparison.Ordinal)) passed++;
                            else if (line.StartsWith("FAIL", StringComparison.Ordinal))
                            {
                                failed++;
                                if (failures.Count < 20) failures.Add(line);
                            }
                        }
                        total = passed + failed;
                    }
                }
                catch (Exception ex)
                {
                    loadError = global::Debug.formatError(ex);
                }
                var sb = new StringBuilder();
                sb.Append("{\"file\":\"").Append(Esc(file)).Append("\",\"total\":").Append(total)
                  .Append(",\"passed\":").Append(passed).Append(",\"failed\":").Append(failed)
                  .Append(",\"loadError\":").Append(Opt(loadError))
                  .Append(",\"runError\":").Append(Opt(runError))
                  .Append(",\"failures\":[");
                for (var i = 0; i < failures.Count; i++)
                {
                    if (i > 0) sb.Append(',');
                    sb.Append('"').Append(Esc(failures[i])).Append('"');
                }
                sb.Append("],\"ms\":").Append((long)sw.Elapsed.TotalMilliseconds).Append('}');
                return sb.ToString();
            }
        }

        // М4: один именованный тест из файла (страница: tests.html?file=…&test=…). Нужно, чтобы гонять
        // в браузере точечные случаи (например «unknown»-ветки Риша), не прогоняя файл целиком.
        [JSExport]
        public static string RunNamedTest(string file, string test)
        {
            lock (testGate)
            {
                var sw = Stopwatch.StartNew();
                var name = Path.GetFileName(file ?? "");
                var err = "";
                try
                {
                    EnsureFiles();
                    var path = Path.Combine(AppContext.BaseDirectory, "tests", name);
                    if (!File.Exists(path))
                        return "{\"file\":\"" + Esc(name) + "\",\"error\":\"нет файла tests/" + Esc(name) + "\"}";
                    var e = Evaluator.newEnv();
                    Evaluator.loadIntoEnv(path, e);
                    var buf = new StringWriter();
                    var oldOut = Console.Out;
                    try
                    {
                        Console.SetOut(buf);
                        Evaluator.eval(List(Sym("run-test"), Types.LispValue.NewLispStr(test ?? "")), e);
                    }
                    finally
                    {
                        Console.SetOut(oldOut);
                    }
                }
                catch (Exception ex)
                {
                    err = global::Debug.formatError(ex);
                }

                return "{\"file\":\"" + Esc(name) + "\",\"test\":\"" + Esc(test ?? "") + "\",\"ms\":" +
                       (long)sw.Elapsed.TotalMilliseconds + ",\"error\":" + Opt(err) + "}";
            }
        }
        // М4: пачка тестов из файла в ОДНОМ окружении (страница: tests.html?file=…&from=…&count=…).
        // Нужна для профиля: загрузка файла платится один раз на пачку, а не на каждый тест.
        [JSExport]
        public static string RunTestSlice(string file, int from, int count)
        {
            lock (testGate)
            {
                var name = Path.GetFileName(file ?? "");
                var sb = new StringBuilder();
                var started = Stopwatch.StartNew();
                sb.Append("{\"file\":\"").Append(Esc(name)).Append("\",\"from\":").Append(from)
                  .Append(",\"count\":").Append(count).Append(",\"tests\":[");
                try
                {
                    EnsureFiles();
                    var path = Path.Combine(AppContext.BaseDirectory, "tests", name);
                    if (!File.Exists(path))
                        return "{\"file\":\"" + Esc(name) + "\",\"error\":\"нет файла tests/" + Esc(name) + "\"}";
                    var text = File.ReadAllText(path);
                    var names = new List<string>();
                    foreach (System.Text.RegularExpressions.Match m in
                             System.Text.RegularExpressions.Regex.Matches(text, "\\(deftest\\s+\"([^\"]+)\""))
                        names.Add(m.Groups[1].Value);

                    var e = Evaluator.newEnv();
                    Evaluator.loadIntoEnv(path, e);
                    var end = Math.Min(names.Count, from + Math.Max(0, count));
                    var first = true;
                    for (var i = Math.Max(0, from); i < end; i++)
                    {
                        var t = Stopwatch.StartNew();
                        var err = "";
                        try
                        {
                            var buf = new StringWriter();
                            var oldOut = Console.Out;
                            try
                            {
                                Console.SetOut(buf);
                                Evaluator.eval(List(Sym("run-test"), Types.LispValue.NewLispStr(names[i])), e);
                            }
                            finally
                            {
                                Console.SetOut(oldOut);
                            }
                        }
                        catch (Exception ex)
                        {
                            err = global::Debug.formatError(ex);
                        }

                        if (!first) sb.Append(',');
                        first = false;
                        sb.Append("{\"test\":\"").Append(Esc(names[i])).Append("\",\"ms\":")
                          .Append((long)t.Elapsed.TotalMilliseconds).Append(",\"error\":").Append(Opt(err)).Append('}');
                    }

                    sb.Append("],\"total\":").Append(names.Count).Append(",\"ms\":")
                      .Append((long)started.Elapsed.TotalMilliseconds).Append('}');
                }
                catch (Exception ex)
                {
                    sb.Append("],\"error\":\"").Append(Esc(global::Debug.formatError(ex))).Append("\"}");
                }

                return sb.ToString();
            }
        }
    }
}
