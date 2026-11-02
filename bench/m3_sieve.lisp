; m3: язык — решето Эратосфена до 2000: vector, v[i] := e, вложенные loop, select (Шаг 21b)
(math-reset)
(math-eval "n := 2000; s := vector(1, k, n); s[1] := 0; i := 2; loop(if(i*i > n, exit), if(s[i] = 1, prog(j := i*i, loop(if(j > n, exit), s[j] := 0, j := j + i))), i := i + 1); dimension(select(s[k] = 1, k, n))")
