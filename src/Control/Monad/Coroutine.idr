module Control.Monad.Coroutine

import public Control.Monad.Coroutine.CPS
import Control.Monad.State
import Data.List1

mutual
  public export
  data CoroutineM : (s : Type) -> (m : Type -> Type) -> (r : Type) -> Type where
    MkCoroutine : m (Either r (Suspended s m r)) -> CoroutineM s m r
  
  public export
  Intermediate : (s : Type) -> (m : Type -> Type) -> (r : Type) -> Type
  Intermediate s m r = Either r (Suspended s m r)

  public export
  Suspended : (s : Type) -> (m : Type -> Type) -> (r : Type) -> Type
  Suspended s m r = (s, Lazy (CoroutineM s m r))

public export
Coroutine : (s : Type) -> (m : Type -> Type) -> (r : Type) -> Type
Coroutine s m = CPS (CoroutineM s m)

public export
interface (Monad m) => ICoroutine (s : Type) (m : Type -> Type) where
  suspend : (s, Lazy (m a)) -> m a

public export
{s : Type} -> {m : Type -> Type} -> (Applicative m, Monad (CoroutineM s m)) =>
ICoroutine s (CoroutineM s m)
where
  suspend = MkCoroutine . pure . Right

public export
{s : Type} -> {m : Type -> Type} -> ICoroutine s m =>
ICoroutine s (CPS m)
where
  suspend t = MkCPS (\h => suspend (map (\(MkCPS p) => p h) t))

resolve :
  {s : Type} -> {m : Type -> Type} -> ICoroutine s (CoroutineM s m) =>
  ({0 m' : Type -> Type} -> ICoroutine s m' => m' a) ->
  CoroutineM s m a
resolve m = runCPS m

pure' : Applicative m => r -> CoroutineM s m r
pure' = MkCoroutine . pure . Left

bind' : Monad m => (a -> CoroutineM s m b) -> CoroutineM s m a -> CoroutineM s m b
bind' f (MkCoroutine ma) = MkCoroutine $ do
  a <- ma
  case a of
    Left  a'      => let MkCoroutine fa' = f a' in fa'
    Right (s, mb) => pure $ Right (s, delay $ bind' f mb)

export
Monad m => Functor (CoroutineM s m) where
  map f ma = bind' (pure' . f) ma

export
Monad m => Applicative (CoroutineM s m) where
  pure      = pure'
  mf <*> ca = bind' (\a => bind' (\f => pure' (f a)) mf) ca

export
covering
Monad m => Monad (CoroutineM s m) where
  ma >>= f = bind' f ma

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

runCoroutineM : CoroutineM s m r -> m (Intermediate s m r)
runCoroutineM (MkCoroutine m) = m

export
runCoroutine : Monad m => Coroutine s m r -> m (Intermediate s m r)
runCoroutine cps = let MkCoroutine m = runCPS cps in m

public export
interface (Semigroup s, Monad m) => Suspension (s : Type) (m : Type -> Type) where
  resumable : s -> m Bool

data Status : (s : Type) -> (m : Type -> Type) -> (r : Type) -> Type where
  Finished     : r               -> Status s m r
  Resumable    : Suspended s m r -> Status s m r
  NotResumable : Suspended s m r -> Status s m r

data TotalStatus : (s : Type) -> (m : Type -> Type) -> (r : Type) -> Type where
  AllFinished   : List r                  -> TotalStatus s m r
  SomeResumable : List1 (Suspended s m r) -> TotalStatus s m r
  Stuck         : List1 (Suspended s m r) -> TotalStatus s m r

select : (Lazy a, Lazy a) -> Bool -> a
select (l, r) b = if b then l else r

parameters {s : Type} {m : Type -> Type} {r : Type} {auto sus : Suspension s m} {auto hasIO : HasIO m} {auto showS : Show s}
  Status'       = Status s m r
  Statuses      = List Status'
  Intermediate' = Intermediate s m r
  Suspended'    = Suspended s m r

  status : Intermediate' -> m Status'
  status (Left  r)         = pure $ Finished r
  status (Right s@(s', _)) = select (Resumable s, NotResumable s) <$> resumable s'

  overallStatus : Statuses -> TotalStatus s m r
  overallStatus [] = AllFinished []
  overallStatus (s@(Finished r)      :: rest) = case overallStatus rest of
    AllFinished   values           => AllFinished   (r :: values)
    SomeResumable resumables       => SomeResumable resumables
    Stuck         nonResumables    => Stuck         nonResumables
  overallStatus (s@(Resumable s')    :: rest) = case overallStatus rest of
    AllFinished   values           => SomeResumable (singleton s')
    SomeResumable resumables       => SomeResumable (cons s' resumables)
    Stuck         nonResumables    => SomeResumable (singleton s')
  overallStatus (s@(NotResumable s') :: rest) = case overallStatus rest of
    AllFinished   values           => Stuck         (singleton s')
    SomeResumable resumables       => SomeResumable resumables
    Stuck         nonResumables    => SomeResumable (cons s' nonResumables)

  bounceStatus : Status' -> m Intermediate'
  bounceStatus (Finished r)            = pure $ Left r
  bounceStatus (NotResumable s)        = pure $ Right s
  bounceStatus (Resumable s@(_, next)) = runCoroutineM next

  showSuspended : Suspended' -> String
  showSuspended (s, _) = "Suspended: " ++ show s

  showIntermediate : Intermediate' -> String
  showIntermediate (Left x)  = "Done!"
  showIntermediate (Right x) = showSuspended x

  mutual
    suspendAll : Statuses -> List1 Suspended' -> Suspended s m (List r)
    suspendAll ss nonResumables = (foldl1 (<+>) $ fst <$> nonResumables, MkCoroutine $ trampoline ss)
    
    trampoline : Statuses -> m (Intermediate s m (List r))
    trampoline []       = pure $ Left []
    trampoline statuses = case overallStatus statuses of
      AllFinished   values           => pure $ Left  $ values
      Stuck         nonResumables    => do
        -- putStrLn "Stuck with non-resumables, suspending..."
        pure $ Right $ suspendAll statuses nonResumables
      SomeResumable resumables       => traverse bounceStatus statuses >>= traverse status >>= trampoline

  export
  concurrent : List (Coroutine s m r) -> Coroutine s m (List r)
  concurrent coroutines = rep $ MkCoroutine $ traverse runCoroutineM (runCPS <$> coroutines) >>= traverse status >>= trampoline
