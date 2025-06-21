module Control.Monad.Coroutine

import public Control.Monad.Coroutine.CPS
import public Control.Monad.Coroutine.Impl
import Control.Monad.Coroutine.Trampoline
import Control.Monad.State

public export
Coroutine : Type -> (Type -> Type) -> Type -> Type
Coroutine s m = CPS (CoroutineImpl s m)

export
suspend : Applicative m => (s, Lazy (Coroutine s m r)) -> Coroutine s m r
suspend sus = MkCPS (\h => MkCoroutine $ pure $ Right $ (map (\(MkCPS p) => p h) sus))

export
MonadTrans (Coroutine s) where
  lift = rep . MkCoroutine . (Left <$>)

export
MonadState stateType m => MonadState stateType (Coroutine s m) where
  get = rep $ MkCoroutine $  Left <$>    get
  put = rep . MkCoroutine . (Left <$>) . put

export
HasIO m => HasIO (Coroutine s m) where
  liftIO = rep . MkCoroutine . liftIO . (Left <$>)

export
runCoroutine : Monad m => Coroutine s m r -> m (Intermediate s m r)
runCoroutine cps = let MkCoroutine m = runCPS cps in m

export
concurrent : Suspension s m => List (Coroutine s m r) -> Coroutine s m (List r)
concurrent coroutines = rep $ MkCoroutine $ traverse runCoroutineImpl (runCPS <$> coroutines) >>= traverse status >>= trampoline
