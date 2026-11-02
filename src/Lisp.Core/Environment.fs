// Окружение переменных — операции над Env
module Environment

open Types

// Создаём пустое окружение
let create () : Env = Env.Empty()

// Добавляем переменную в текущую область видимости
let define (env: Env) (name: string) (value: LispValue) : Env =
    env.Define name value

// Ищем переменную по имени, поднимаясь по цепочке окружений
let lookup (env: Env) (name: string) : LispValue option =
    env.Lookup name

// Расширяем окружение новыми парами (для вызова функции)
let extend (env: Env) (pairs: (string * LispValue) list) : Env =
    env.Extend pairs
