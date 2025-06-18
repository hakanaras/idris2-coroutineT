module Control.Monad.Coroutine

import Control.Monad.State

mutual
  export
  data CoroutineT : (s, m : Type -> Type) -> (r : Type) -> Type where
    MkCoroutineT : m (Intermediate s m r) -> CoroutineT s m r

  ||| An intermediate result type for coroutines. Defined as an Either type where
  ||| Left represents a finished result and Right represents a suspended coroutine.
  public export
  Intermediate : (s, m : Type -> Type) -> (r : Type) -> Type
  Intermediate s m r = Either r (Suspended s m r)

  public export
  Suspended : (s, m : Type -> Type) -> (r : Type) -> Type
  Suspended s m r = s (Lazy (CoroutineT s m r))

export
runCoroutineT : CoroutineT s m r -> m (Intermediate s m r)
runCoroutineT (MkCoroutineT m) = m

unwrap : CoroutineT s m r -> m (Intermediate s m r)
unwrap (MkCoroutineT ma) = ma

eitherM : Monad m => Lazy (a -> m c) -> Lazy (b -> m c) -> m (Either a b) -> m c
eitherM f g = (>>= either f g)

eitherM' : Monad m => m (Either a b) -> Lazy (a -> m c) -> Lazy (b -> m c) -> m c
eitherM' me f g = eitherM f g me

mapLazy : Functor f => (a -> b) -> f (Lazy a) -> f (Lazy b)
mapLazy f = map $ delay . f . force

export
(Functor s, Monad m) => Functor (CoroutineT s m) where
  map f (MkCoroutineT ma) = MkCoroutineT $ eitherM' ma
    (pure . Left . f)
    (pure . Right . mapLazy (map f))

export
(Functor s, Monad m) => Applicative (CoroutineT s m) where
  pure = MkCoroutineT . pure . Left
  MkCoroutineT mf <*> ca = MkCoroutineT $ eitherM' mf
    (unwrap . (<$> ca))
    (pure . Right . mapLazy (<*> ca))

export
covering
(Functor s, Monad m) => Monad (CoroutineT s m) where
  MkCoroutineT ma >>= f = MkCoroutineT $ eitherM' ma
    (unwrap . f)
    (pure . Right . mapLazy (>>= f))

export
(Functor s, MonadState stateType m) => MonadState stateType (CoroutineT s m) where
  get = MkCoroutineT $ get >>= pure . Left
  put = MkCoroutineT . (>> pure (Left ())) . put

export
(Functor s, HasIO m) => HasIO (CoroutineT s m) where
  liftIO = MkCoroutineT . liftIO . map Left

export
suspend : Applicative m => Suspended s m r -> CoroutineT s m r
suspend = MkCoroutineT . pure . Right

public export
interface (Functor s, Monad m) => Suspension (s : Type -> Type) (m : Type -> Type) where
  fold      : List (s a) -> b -> s b
  resume    : Suspended s m r -> CoroutineT s m r
  resumable : Suspended s m r -> m Bool
  resumable _ = pure True

data Status : (s, m : Type -> Type) -> (r : Type) -> Type where
  Finished     : r                    -> Status s m r
  Resumable    : Suspended s m r      -> Status s m r
  NotResumable : Suspended s m r      -> Status s m r

data TotalStatus : (s, m : Type -> Type) -> (r : Type) -> Type where
  AllFinished   : List r                  -> TotalStatus s m r
  SomeResumable : List (Status s m r)     -> TotalStatus s m r
  Stuck         : List (Status s m r)     -> TotalStatus s m r

parameters {s, m : Type -> Type} {r : Type} {auto sus : Suspension s m}
  -- Type aliases for readability:
  Status' = Status s m r
  Statuses = List Status'
  Intermediate' = Intermediate s m r
  Suspended' = Suspended s m r

  ||| This converts an `Intermediate` result into a `Status` for easier handling.
  status : Intermediate' -> m Status'
  status (Left r)  = pure $ Finished r
  status (Right s) = resumable s <&> \x => if x then Resumable s else NotResumable s

  ||| Given a list of subroutine statuses, this will return the status of the overall coroutine.
  ||| It will return AllFinished if all subroutines are finished, SomeResumable if there are resumable
  ||| subroutines, and Stuck if there are no resumable subroutines but some are not finished.
  overallStatus : Statuses -> TotalStatus s m r
  overallStatus [] = AllFinished []
  overallStatus (s@(Finished r)      :: rest) = case overallStatus rest of
    AllFinished   rest' => AllFinished   (r  :: rest')
    SomeResumable rest' => SomeResumable (s  :: rest')
    Stuck         rest' => Stuck         (s  :: rest')
  overallStatus (s'@(Resumable _)    :: rest) = case overallStatus rest of
    AllFinished   rest' => SomeResumable (s' :: (Finished <$> rest'))
    SomeResumable rest' => SomeResumable (s' :: rest')
    Stuck         rest' => SomeResumable (s' :: rest')
  overallStatus (s'@(NotResumable _) :: rest) = case overallStatus rest of
    AllFinished   rest' => Stuck         (s' :: (Finished <$> rest'))
    SomeResumable rest' => SomeResumable (s' :: rest')
    Stuck         rest' => Stuck         (s' :: rest')

  ||| This is applied to each subroutine during a bounce on the trampoline.
  ||| It will run resumable subroutines again and leave everything else as is.
  bounceStatus : Status' -> m Intermediate'
  bounceStatus (Finished r)     = pure $ Left r
  bounceStatus (NotResumable s) = pure $ Right s
  bounceStatus (Resumable s)    = let MkCoroutineT mr = resume s in mr

  ||| Binder for getting all non-resumable subroutines from a list of statuses.
  ||| Used to collect all "suspension reasons" and fold them for the overall coroutine suspension.
  nonResumables : Status' -> List Suspended'
  nonResumables (NotResumable x) = [x]
  nonResumables _                = []

  mutual
    ||| In the case that the overall coroutine is stuck, this will return a suspension
    ||| combining the suspensions of all unfinished, non-resumable subroutines.
    suspendAll : Statuses -> Suspended s m (List r)
    suspendAll ss = fold @{sus} (ss >>= nonResumables) (delay $ MkCoroutineT $ trampoline ss)
    
    ||| Recursive implementation of a "trampoline":
    ||| Keeps bouncing subroutines until either all of them are finished or none are resumable.
    trampoline : Statuses -> m (Intermediate s m (List r))
    trampoline []       = pure $ Left []
    trampoline statuses = case overallStatus statuses of
      AllFinished   rs => pure $ Left rs
      Stuck         ss => pure $ Right $ suspendAll ss
      SomeResumable ss => traverse bounceStatus ss >>= traverse status >>= trampoline

  export
  concurrent : List (CoroutineT s m r) -> CoroutineT s m (List r)
  concurrent coroutines = MkCoroutineT $ traverse unwrap coroutines >>= traverse status >>= trampoline
