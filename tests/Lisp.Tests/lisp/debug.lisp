; Lisp-тесты отладки, шаг D3c: режим проглоченных ошибок (set-debug! / swallowed-errors / debug-mode?).
; Важно: тесты одного файла делят окружение — состояние Debug глобально на процесс; восстанавливаем в конце.

(deftest "отладка/D3c: включённый режим ловит ошибку внутри try"
  (set-debug! #t)
  ; try с обработчиком глотает ошибку — но в режиме она фиксируется
  (assert-equal (try (car 5) (lambda (e) 'caught)) 'caught)
  (assert-true (member? "car: ожидается список, получено 5 | в car" (swallowed-errors)))
  (set-debug! #f))

(deftest "отладка/D3c: включённый режим ловит ошибку внутри sum-guard"
  ; каскад sum-symbolic: стратегии (Госпер/Абрамов/Цайльбергер) через sum-guard глотают ошибки —
  ; в режиме они видны в swallowed-errors (здесь: негипергеометрический терм поднимает ошибку);
  ; форма ответа не проверяется (линейность даёт невычисленную форму)
  (set-debug! #t)
  (sum-symbolic '(* 2 (undefined-fn-d3c k)) 'k 0 'n)
  (assert-true (>= (length (swallowed-errors)) 1))
  (set-debug! #f))

(deftest "отладка/D3c: выключенный режим ничего не печатает"
  (set-debug! #f)
  (assert-true (not (debug-mode?)))
  ; try глотает ошибку, буфер проглоченных пуст
  (assert-equal (try (car 5) (lambda (e) 'caught)) 'caught)
  (assert-equal (swallowed-errors) '()))

; тесты одного файла могут идти параллельно (Theory): состояние Debug глобально на процесс,
; восстановление — в конце каждого теста; это же делает загрузка файла (строка ниже)
(set-debug! #f)
