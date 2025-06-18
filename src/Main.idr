module Main

import Data.SortedMap
import Data.String
import Control.Monad.Coroutine
import Control.Monad.State

Scope = SortedMap String String
InnerMonad = StateT Scope IO

data Await : (a : Type) -> Type where
  MkAwait : List String -> a -> Await a

MyCoroutine = CoroutineT Await InnerMonad

Functor Await where
  map f (MkAwait keys b) = MkAwait keys (f b)

Suspension Await InnerMonad where
  resume    (MkAwait _ s)    = s
  resumable (MkAwait keys _) = do
    scope <- get
    let result = any (\key => case lookup key scope of { Just _ => True; Nothing => False }) keys
    pure result
  fold as b = MkAwait (foldl f [] as) b
    where
      f : List String -> Await a -> List String
      f acc (MkAwait keys _) = acc ++ keys


runMyCoroutine : MyCoroutine a -> IO (Intermediate Await InnerMonad a)
runMyCoroutine mc = snd <$> runStateT empty (runCoroutineT mc)

getScope : MyCoroutine Scope
getScope = get

lookupVar : String -> MyCoroutine String
lookupVar key = do
  scope <- getScope
  case lookup key scope of
    Just value => pure value
    Nothing    => suspend $ MkAwait [key] (delay $ lookupVar key)

putVar : String -> String -> MyCoroutine ()
putVar key value = do
  scope <- get
  put $ insert key value scope
  pure ()

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
