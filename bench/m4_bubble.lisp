; m4: язык — пузырьковая сортировка 200 элементов в функции с локальными переменными и v[i] := e (Шаг 21b)
(math-reset)
(math-eval "bsort(v, n, i := 1, j := 1, t := 0) := prog(loop(if(i > n - 1, exit), j := 1, loop(if(j > n - i, exit), if(v[j] > v[j + 1], prog(t := v[j], v[j] := v[j + 1], v[j + 1] := t)), j := j + 1), i := i + 1), v); w := vector(mod(k*7919, 211), k, 200); r := bsort(w, 200); r[1] + r[200]")
