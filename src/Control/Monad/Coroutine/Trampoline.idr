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

overallStatus : List (Status s m r) -> TotalStatus s m r
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

bounceStatus : Applicative m => Status s m r -> m (Intermediate s m r)
bounceStatus (Finished r)            = pure $ Left r
bounceStatus (NotResumable s)        = pure $ Right s
bounceStatus (Resumable s@(_, next)) = runCoroutineImpl next

parameters {0 s : Type} {0 m : Type -> Type} {0 r : Type} {auto sus : Suspension s m}
  export
  status : Intermediate s m r -> m (Status s m r)
  status (Left  r)         = pure $ Finished r
  status (Right s@(s', _)) = (\r => if r then Resumable s else NotResumable s) <$> resumable s'

  mutual
    suspendAll : List (Status s m r) -> List1 (Suspended s m r) -> Suspended s m (List r)
    suspendAll ss nonResumables = (foldr1 (<+>) $ fst <$> nonResumables, MkCoroutine $ trampoline ss)
    
    export
    trampoline : List (Status s m r) -> m (Intermediate s m (List r))
    trampoline []       = pure $ Left []
    trampoline statuses = case overallStatus statuses of
      AllFinished   values           => pure $ Left  $ values
      Stuck         nonResumables    => pure $ Right $ suspendAll statuses nonResumables
      SomeResumable resumables       => traverse bounceStatus statuses >>= traverse status >>= trampoline
