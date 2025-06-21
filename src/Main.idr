module Main

import Data.Maybe
import Data.List1
import Data.SortedMap
import Data.String
import Control.Monad.State
import Control.Monad.Coroutine

Scope = SortedMap String String
InnerMonad = StateT Scope IO

record Await where
  constructor MkAwait
  keys : List1 String

MyCoroutine = Coroutine Await InnerMonad

runMyCoroutine : MyCoroutine a -> IO (Intermediate Await InnerMonad a)
runMyCoroutine mc = snd <$> runStateT (Data.SortedMap.empty) (runCoroutine mc)

getScope : MyCoroutine Scope
getScope = get

containsKey : Scope -> String -> Bool
containsKey scope key = isJust $ lookup key scope

Semigroup Await where
  MkAwait keys1 <+> MkAwait keys2 = MkAwait (keys1 <+> keys2)

Suspension Await InnerMonad where
  resumable (MkAwait keys) = (\scope => any (containsKey scope) keys) <$> get

lookupVar : String -> MyCoroutine String
lookupVar key = do
  scope <- getScope
  case lookup key scope of
    Just value => pure value
    Nothing    => suspend $ (MkAwait (singleton key), lookupVar key)

putVar : String -> String -> MyCoroutine ()
putVar key value = getScope >>= put . insert key value

Show Await where
  show (MkAwait keys) = show keys

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
  -- putVar "b1" "Bar"
  b0 <- lookupVar "b0"
  pure $ "( Task 1 is done: " ++ a0 ++ " " ++ b0 ++ " )"

stackUnsafeTask : String -> String -> Int -> MyCoroutine (List String)
stackUnsafeTask myPrefix otherPrefix num = do
  putVar (myPrefix ++ show num) (show myPrefix ++ " " ++ show num)
  other <- lookupVar (otherPrefix ++ show num)
  if num > 0
    then (other ::) <$> stackUnsafeTask myPrefix otherPrefix (num - 1)
    else pure [other]

printIntermediate : Show a => Intermediate Await InnerMonad a -> String
printIntermediate (Left result)             = "Result: " ++ show result
printIntermediate (Right (MkAwait keys, _)) = "Coroutine is waiting for: " ++ joinBy ", " (toList keys)

main : IO ()
main = do
  eitherResult <- (runMyCoroutine $ joinBy ", " <$> concurrent [task0, task1])
  putStrLn $ printIntermediate eitherResult
  stackSafeResult <- runMyCoroutine $ joinBy ", " <$> (show . length <$>) <$> concurrent [stackUnsafeTask "0" "1" 1000000, stackUnsafeTask "1" "0" 1000000]
  putStrLn $ printIntermediate stackSafeResult
