module Control.Monad.Coroutine.Trampoline

import Control.Monad.Coroutine.Impl
import Data.List1

data Status : Type -> (Type -> Type) -> Type -> Type where
  Finished     : r               -> Status s m r
  Resumable    : Suspended s m r -> Status s m r
  NotResumable : Suspended s m r -> Status s m r

data TotalStatus : Type -> (Type -> Type) -> Type -> Type where
  AllFinished   : List r                  -> TotalStatus s m r
  SomeResumable : List1 (Suspended s m r) -> TotalStatus s m r
  Stuck         : List1 (Suspended s m r) -> TotalStatus s m r

parameters {s : Type} {m : Type -> Type} {r : Type} {auto sus : Suspension s m}
  Status'       = Status s m r
  Statuses      = List Status'
  Intermediate' = Intermediate s m r
  Suspended'    = Suspended s m r

  export
  status : Intermediate' -> m Status'
  status (Left  r)         = pure $ Finished r
  status (Right s@(s', _)) = (\r => if r then Resumable s else NotResumable s) <$> resumable s'

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
  bounceStatus (Resumable s@(_, next)) = runCoroutineImpl next

  mutual
    suspendAll : Statuses -> List1 Suspended' -> Suspended s m (List r)
    suspendAll ss nonResumables = (foldl1 (<+>) $ fst <$> nonResumables, MkCoroutine $ trampoline ss)
    
    export
    trampoline : Statuses -> m (Intermediate s m (List r))
    trampoline []       = pure $ Left []
    trampoline statuses = case overallStatus statuses of
      AllFinished   values           => pure $ Left  $ values
      Stuck         nonResumables    => pure $ Right $ suspendAll statuses nonResumables
      SomeResumable resumables       => traverse bounceStatus statuses >>= traverse status >>= trampoline
