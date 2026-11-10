; m1: язык — сумма 1..10^5 циклом loop над глобальными переменными (Шаг 21b)
(math-reset)
(math-eval "set_loop_limit(1000000); s := 0; k := 1; loop(if(k > 100000, exit), s := s + k, k := k + 1); s")
