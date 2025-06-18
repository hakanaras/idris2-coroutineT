# Control.Monad.Coroutine

## CoroutineT

Library that provides a coroutine monad transformer, which is a computation that can suspend itself any number of times, before eventually producing a result.

`CoroutineT : (s, m : Type -> Type) -> (r : Type) -> Type`

where:

`s` is a user-provided type constructor for a suspended state. It can contain a "reason" for the suspension and a coroutine describing how to resume the computation (the type parameter), among other things.

`m` is the inner monad. This will likely need some StateT or ReaderT flavour to determine when coroutines can be resumed.

`r` is the type of the produced result.

## concurrent

Also provided is a function for concurrent execution of interdependent coroutines:

`concurrent : List (CoroutineT s m r) -> CoroutineT s m (List r)`

A special case of `traverse`. It "trampolines" any number of subroutines, i.e. it runs them all and repeatedly resumes them until either:

- All subroutines are finished, in which case their results are combined and returned. Or
- The only remaining unfinished subroutines are not resumable according to some criterium provided by the user.

The point of this function is to be able to run multiple routines that may depend on eachother non-trivially (e.g. syntax analysis on multiple mutually dependent modules/definitions), without having to determine beforehand how exactly they depend on eachother.

## Example:

Check `Main.idr` for a full sample, but in short:

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
    Left  result          => "Result: " ++ joinBy ", " result
    Right (MkAwait key _) => "Coroutine is waiting for: " ++ joinBy ", " key
```

Output: ``

If we comment one of the `putVar`s: ``

Output: ``