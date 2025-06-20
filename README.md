# Control.Monad.Coroutine

## Coroutine

A coroutine monad transformer, i.e. a computation that can suspend itself any number of times, before eventually producing a result.

`Coroutine : (s : Type) -> (m : Type -> Type) -> (r : Type) -> Type`

where:

`s` is a user-provided type for a suspended state. It's intended to contain a reason for the suspension.

`m` is the inner monad. This will likely need some `State` or `IO` flavour to determine when coroutines can be resumed.

`r` is the type of the produced result.

## concurrent

Also provided is a function for concurrent execution of interdependent coroutines:

`concurrent : List (Coroutine s m r) -> Coroutine s m (List r)`

A special case of `traverse`. It "trampolines" any number of subroutines, i.e. it runs them all and repeatedly resumes them until either:

- all subroutines are finished, in which case their results are combined and returned. Or
- the only remaining unfinished subroutines are not resumable according to a user-provided criterium, in which case the overall coroutine is suspended with the reasons combined.

The point of this function is to be able to run multiple routines that may depend on eachother non-trivially (e.g. syntax analysis on multiple mutually dependent modules/definitions), without having to determine beforehand how exactly they depend on eachother.

## Example

Check `Main.idr` for a full sample (including a demonstration of stack-safety), but in short:

```
task0 : MyCoroutine String
task0 = do
  putVar "a0" "Hello"
  a1 <- lookupVar "a1"
  putVar "b0" "World"
  b1 <- lookupVar "b1"
  pure $ "( Task 0 is done: " ++ a1 ++ " " ++ b1 ++ " )"

task1 : MyCoroutine String
task1 = do
  putVar "a1" "Foo"
  a0 <- lookupVar "a0"
  putVar "b1" "Bar"
  b0 <- lookupVar "b0"
  pure $ "( Task 1 is done: " ++ a0 ++ " " ++ b0 ++ " )"

main : IO ()
main = do
  eitherResult <- runMyCoroutine $ concurrent [task0, task1]
  putStrLn $ case eitherResult of
    Left  result            => "Result: " ++ joinBy ", " result
    Right (MkAwait keys, _) => "Coroutine is waiting for: " ++ joinBy ", " (toList keys)
```

Output: `Result: ( Task 0 is done: Foo Bar ), ( Task 1 is done: Hello World )`

Or if we interrupt the flow by commenting this line:

```
-- putVar "b1" "Bar"
```

Output: `Coroutine is waiting for: b1`